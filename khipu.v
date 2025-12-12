(******************************************************************************)
(*                                                                            *)
(*         Khipu Numerals: Inka Knot Records and Decimal Positional Semantics *)
(*                                                                            *)
(*  A verified formalization of the numerical encoding system used in khipu   *)
(*  (Quechua: "knot"), the knotted-cord recording devices of the Inka Empire  *)
(*  and predecessor Andean civilizations (c. 2600 BCE - 1532 CE).             *)
(*                                                                            *)
(*  "He who seeks to count the stars before he can count the scores and       *)
(*   knots of the quipus deserves derision." - Inca Garcilaso de la Vega,     *)
(*   Comentarios Reales de los Incas, 1609.                                   *)
(*                                                                            *)
(*  Author: Charles C. Norton                                                 *)
(*  Date: December 2025                                                       *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  Arith.Arith
  Arith.PeanoNat
  Bool.Bool
  Lists.List
  Program.Equality
  Vectors.Vector
  Vectors.Fin
  micromega.Lia.

Import ListNotations.
Import VectorNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Khipu.

(* ========================================================================== *)
(*                                  GEOMETRY                                  *)
(* ========================================================================== *)

(* Pendant cords hang vertically from the primary cord. Knot positions are
   measured from the free end (bottom) upward. The units place is at the
   bottom, with tens, hundreds, etc. ascending toward the attachment point.
   This bottom-to-top ordering was documented by Locke (1923) and confirmed
   through analysis of hundreds of extant khipu specimens. *)

Definition pos : Type := nat.

Record Interval : Type := {
  lo : pos;               (* inclusive *)
  hi : pos;               (* exclusive *)
  lo_lt_hi : lo < hi
}.

(* Half-open membership: lo <= p < hi *)
Definition in_interval (p : pos) (Iv : Interval) : Prop :=
  lo Iv <= p < hi Iv.

Definition in_intervalb (p : pos) (Iv : Interval) : bool :=
  (lo Iv <=? p) && (p <? hi Iv).

Lemma in_intervalb_spec : forall p Iv,
  in_intervalb p Iv = true <-> in_interval p Iv.
Proof.
  intros p Iv. unfold in_intervalb, in_interval.
  rewrite andb_true_iff.
  rewrite Nat.leb_le, Nat.ltb_lt.
  tauto.
Qed.

Lemma not_in_interval_if_ge_hi : forall Iv p,
  hi Iv <= p -> ~ in_interval p Iv.
Proof.
  intros Iv p Hge [Hlo Hlt]. lia.
Qed.

Lemma not_in_interval_if_lt_lo : forall Iv p,
  p < lo Iv -> ~ in_interval p Iv.
Proof.
  intros Iv p Hlt [Hlo _]. lia.
Qed.

(* Ordered, non-overlapping registers are expressed as hi Iv <= lo Jv.
   These two separation lemmas support both directions of exclusion. *)
Lemma interval_after_excludes :
  forall Iv Jv p,
    hi Iv <= lo Jv ->
    in_interval p Jv ->
    ~ in_interval p Iv.
Proof.
  intros Iv Jv p Hsep [HloJ HhiJ] [HloI HhiI]. lia.
Qed.

Lemma interval_before_excludes :
  forall Iv Jv p,
    hi Iv <= lo Jv ->
    in_interval p Iv ->
    ~ in_interval p Jv.
Proof.
  intros Iv Jv p Hsep [HloI HhiI] [HloJ HhiJ]. lia.
Qed.

(* "Wide enough" interval to host 10 canonical slot positions: lo+1+0 .. lo+1+9. *)
Definition wide_enough (Iv : Interval) : Prop :=
  lo Iv + 11 <= hi Iv.

Definition slot (Iv : Interval) (k : nat) : pos :=
  lo Iv + 1 + k.

Lemma slot_in_interval :
  forall Iv k,
    k < 10 ->
    wide_enough Iv ->
    in_interval (slot Iv k) Iv.
Proof.
  intros Iv k Hk Hwide.
  unfold in_interval, slot.
  split.
  - lia.
  - assert (k <= 9) by lia.
    unfold wide_enough in Hwide.
    lia.
Qed.

(* ========================================================================== *)
(*                                   DIGITS                                   *)
(* ========================================================================== *)

(* Decimal digit: canonical 0..9 type. *)
Definition digit : Type := Fin.t 10.

Definition digit_to_nat (d : digit) : nat := proj1_sig (Fin.to_nat d).

Lemma digit_to_nat_lt10 : forall d : digit, digit_to_nat d < 10.
Proof. intro d. unfold digit_to_nat. exact (proj2_sig (Fin.to_nat d)). Defined.

Lemma digit_ext : forall a b : digit,
  digit_to_nat a = digit_to_nat b -> a = b.
Proof.
  apply Fin.to_nat_inj.
Qed.

Definition digit_of_nat : forall (n : nat), n < 10 -> digit :=
  fun n H => @Fin.of_nat_lt n 10 H.
Arguments digit_of_nat n H : clear implicits.

Lemma lt_0_10 : 0 < 10. Proof. lia. Qed.
Lemma lt_1_10 : 1 < 10. Proof. lia. Qed.

Definition digit0 : digit := digit_of_nat 0 lt_0_10.
Definition digit1 : digit := digit_of_nat 1 lt_1_10.

Lemma digit_to_nat_of_nat_lt :
  forall n (H : n < 10),
    digit_to_nat (digit_of_nat n H) = n.
Proof.
  intros n H.
  unfold digit_to_nat, digit_of_nat.
  rewrite Fin.to_nat_of_nat.
  reflexivity.
Qed.

Lemma digit_of_nat_to_nat : forall d : digit,
  digit_of_nat (digit_to_nat d) (digit_to_nat_lt10 d) = d.
Proof.
  intros d.
  unfold digit_of_nat, digit_to_nat.
  apply Fin.of_nat_to_nat_inv.
Qed.

(* ========================================================================== *)
(*                                 KNOT FORMS                                 *)
(* ========================================================================== *)

(* Knots can be tied in two mirror-image orientations. Following Urton (2003),
   we call these S-twist and Z-twist, based on the diagonal direction of the
   cord fibers. Hyland (2014) demonstrated that S/Z correlates with Andean
   moiety organization: S-knots mark Hanan (upper) and Z-knots mark Urin
   (lower) social divisions. *)

Inductive Twist : Type := TS | TZ.

(* Long knots encode digits 2-9 via the number of turns. A long knot with
   only 1 turn is physically indistinguishable from an overhand knot, hence
   the range 2-9. This constraint was noted by Locke (1923) and formalized
   by Ascher & Ascher (1981). *)

Record Turns : Type := {
  tval : nat;
  t_range : 2 <= tval <= 9
}.

Lemma turns_lt10 : forall t : Turns, tval t < 10.
Proof.
  intros [v [H2 H9]]. simpl. lia.
Qed.

(* The three knot types used in numerical khipu, per Locke (1923):
   - Overhand: simple knot, used in clusters for tens/hundreds/etc.
   - Long: 2-9 turns, encodes digits 2-9 in the units place only.
   - FigureEight: encodes digit 1 in the units place (since Long cannot). *)

Inductive KnotKind : Type :=
| Overhand
| Long (t : Turns)
| FigureEight.

Record Knot : Type := {
  k_pos   : pos;
  k_kind  : KnotKind;
  k_twist : Twist
}.

Definition is_overhandb (k : Knot) : bool :=
  match k_kind k with
  | Overhand => true
  | _ => false
  end.

Definition all_overhandb (ks : list Knot) : bool :=
  forallb is_overhandb ks.

Lemma all_overhandb_spec :
  forall ks,
    all_overhandb ks = true <->
    (forall k, List.In k ks -> k_kind k = Overhand).
Proof.
  intro ks. unfold all_overhandb.
  rewrite forallb_forall.
  split.
  - intros H k Hin. specialize (H k Hin).
    unfold is_overhandb in H.
    destruct (k_kind k); try discriminate; reflexivity.
  - intros H k Hin. specialize (H k Hin).
    unfold is_overhandb. now rewrite H.
Qed.

(* ========================================================================== *)
(*                            REGISTERS / LAYOUTS                              *)
(* ========================================================================== *)

(* Ordered, disjoint, bottom-to-top register intervals. Index 0 = units. *)
Definition head_interval {n : nat} (regs : Vector.t Interval (Datatypes.S n)) : Interval :=
  Vector.hd regs.

Fixpoint chain_order {n : nat} (regs : Vector.t Interval n) {struct regs} : Prop :=
  match regs with
  | [] => True
  | Iv :: tl =>
      match tl as tl0 return Prop with
      | [] => True
      | Jv :: _ => hi Iv <= lo Jv /\ chain_order tl
      end
  end.

Fixpoint all_wide {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => True
  | Iv :: tl => wide_enough Iv /\ all_wide tl
  end.

Fixpoint all_within (len : pos) {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => True
  | Iv :: tl => hi Iv <= len /\ all_within len tl
  end.

Record NumeralSpec (n : nat) : Type := {
  ns_len      : pos;
  ns_len_pos  : 0 < ns_len;
  ns_regs     : Vector.t Interval n;
  ns_order    : chain_order ns_regs;
  ns_wide     : all_wide ns_regs;
  ns_within   : all_within ns_len ns_regs
}.

Lemma chain_order_tail :
  forall n (Iv : Interval) (tl : Vector.t Interval n),
    chain_order (Iv :: tl) -> chain_order tl.
Proof.
  intros n Iv tl Hord.
  destruct tl as [|Jv n' tl']; simpl in *; auto.
  destruct Hord as [_ Htl]. exact Htl.
Qed.

Lemma all_wide_tail :
  forall n (Iv : Interval) (tl : Vector.t Interval n),
    all_wide (Iv :: tl) -> all_wide tl.
Proof.
  intros n Iv tl H. simpl in H. tauto.
Qed.

Lemma all_within_tail :
  forall len n (Iv : Interval) (tl : Vector.t Interval n),
    all_within len (Iv :: tl) -> all_within len tl.
Proof.
  intros len n Iv tl H. simpl in H. tauto.
Qed.

Lemma all_wide_nth :
  forall n (regs : Vector.t Interval n) (i : Fin.t n),
    all_wide regs ->
    wide_enough (Vector.nth regs i).
Proof.
  induction regs as [|Iv m tl IH]; intros i Hwide.
  - inversion i.
  - simpl in Hwide. destruct Hwide as [Hh Ht].
    dependent destruction i; simpl; [exact Hh|].
    apply IH. exact Ht.
Qed.

Lemma all_within_nth :
  forall len n (regs : Vector.t Interval n) (i : Fin.t n),
    all_within len regs ->
    hi (Vector.nth regs i) <= len.
Proof.
  induction regs as [|Iv m tl IH]; intros i Hwithin.
  - inversion i.
  - simpl in Hwithin. destruct Hwithin as [Hh Ht].
    dependent destruction i; simpl; [exact Hh|].
    apply IH. exact Ht.
Qed.

(* In a chain-ordered vector, the head interval is before every tail interval. *)
Lemma chain_order_head_before_nth :
  forall n (Iv : Interval) (tl : Vector.t Interval n) (i : Fin.t n),
    chain_order (Iv :: tl) ->
    hi Iv <= lo (Vector.nth tl i).
Proof.
  intros n Iv tl.
  revert Iv.
  induction tl as [|Jv m tl IH]; intros Iv i Hord.
  - inversion i.
  - simpl in Hord. destruct Hord as [Hij Htail].
    dependent destruction i; simpl.
    + exact Hij.
    + pose proof (lo_lt_hi Jv) as Hlt.
      assert (hi Iv <= hi Jv) by lia.
      specialize (IH Jv i Htail).
      lia.
Qed.

(* ========================================================================== *)
(*                              KNOT GROUPING                                 *)
(* ========================================================================== *)

Definition knots_in (Iv : Interval) (ks : list Knot) : list Knot :=
  filter (fun k => in_intervalb (k_pos k) Iv) ks.

Lemma knots_in_app : forall Iv xs ys,
  knots_in Iv (List.app xs ys) = List.app (knots_in Iv xs) (knots_in Iv ys).
Proof.
  intros Iv xs ys. unfold knots_in. now rewrite filter_app.
Qed.

Lemma knots_in_sound : forall Iv ks k,
  List.In k (knots_in Iv ks) -> in_interval (k_pos k) Iv.
Proof.
  intros Iv ks k Hin.
  unfold knots_in in Hin.
  apply filter_In in Hin as [HinK Hb].
  apply (proj1 (in_intervalb_spec _ _)) in Hb.
  exact Hb.
Qed.

Lemma knots_in_complete : forall Iv ks k,
  List.In k ks ->
  in_interval (k_pos k) Iv ->
  List.In k (knots_in Iv ks).
Proof.
  intros Iv ks k HinK HinI.
  unfold knots_in.
  apply filter_In.
  split; [assumption|].
  apply (proj2 (in_intervalb_spec _ _)).
  exact HinI.
Qed.

Definition outside_interval (Iv : Interval) (ks : list Knot) : Prop :=
  forall k, List.In k ks -> ~ in_interval (k_pos k) Iv.

Lemma knots_in_self :
  forall Iv ks,
    (forall k, List.In k ks -> in_interval (k_pos k) Iv) ->
    knots_in Iv ks = ks.
Proof.
  intros Iv ks Hall.
  unfold knots_in.
  induction ks as [|a tl IH]; simpl; auto.
  assert (Ha : in_interval (k_pos a) Iv).
  { apply Hall. now left. }
  assert (Hb : in_intervalb (k_pos a) Iv = true).
  { apply (proj2 (in_intervalb_spec _ _)). exact Ha. }
  rewrite Hb. f_equal.
  apply IH. intros k Hin. apply Hall. now right.
Qed.

Lemma knots_in_none :
  forall Iv ks,
    outside_interval Iv ks ->
    knots_in Iv ks = @List.nil Knot.
Proof.
  intros Iv ks Hout.
  unfold knots_in.
  induction ks as [|a tl IH].
  - reflexivity.
  - simpl.
    assert (Ha : ~ in_interval (k_pos a) Iv).
    { apply Hout. now left. }
    destruct (in_intervalb (k_pos a) Iv) eqn:Hb.
    + exfalso. apply (proj1 (in_intervalb_spec _ _)) in Hb. exact (Ha Hb).
    + apply IH. intros k Hink. apply Hout. now right.
Qed.

Lemma knots_in_app_left_outside_interval :
  forall Iv xs ys,
    outside_interval Iv xs ->
    knots_in Iv (List.app xs ys) = knots_in Iv ys.
Proof.
  intros Iv xs ys Hout.
  rewrite knots_in_app.
  rewrite (knots_in_none (Iv:=Iv) (ks:=xs) Hout).
  reflexivity.
Qed.

(* ========================================================================== *)
(*                      COVERAGE AND UNIQUE PLACE ASSIGNMENT                   *)
(* ========================================================================== *)

Fixpoint regs_covered (p : pos) {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => False
  | Iv :: tl => in_interval p Iv \/ regs_covered p tl
  end.

Fixpoint regs_coveredb (p : pos) {n : nat} (regs : Vector.t Interval n) : bool :=
  match regs with
  | [] => false
  | Iv :: tl => in_intervalb p Iv || regs_coveredb p tl
  end.

Lemma regs_coveredb_spec : forall p n (regs : Vector.t Interval n),
  regs_coveredb p regs = true <-> regs_covered p regs.
Proof.
  intros p n regs.
  induction regs as [|Iv m tl IH]; simpl.
  - split; intro H; inversion H.
  - rewrite orb_true_iff. rewrite in_intervalb_spec. rewrite IH. tauto.
Qed.

Lemma regs_covered_exists_index :
  forall n (regs : Vector.t Interval n) p,
    regs_covered p regs ->
    exists i : Fin.t n, in_interval p (Vector.nth regs i).
Proof.
  induction regs as [|Iv n tl IH]; intros p Hcov.
  - contradiction.
  - simpl in Hcov. destruct Hcov as [Hin|Hcov].
    + exists Fin.F1. simpl. exact Hin.
    + destruct (IH p Hcov) as [i Hi].
      exists (Fin.FS i). simpl. exact Hi.
Qed.

Fixpoint place_of_pos {n : nat} (p : pos) (regs : Vector.t Interval n)
  : option (Fin.t n) :=
  match regs with
  | [] => None
  | Iv :: tl =>
      if in_intervalb p Iv
      then Some Fin.F1
      else option_map Fin.FS (place_of_pos p tl)
  end.

Lemma place_of_pos_sound :
  forall n (regs : Vector.t Interval n) p i,
    place_of_pos p regs = Some i ->
    in_interval p (Vector.nth regs i).
Proof.
  induction regs as [|Iv n tl IH]; intros p i H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (in_intervalb p Iv) eqn:Hb.
    + inversion H. subst i.
      apply (proj1 (in_intervalb_spec _ _)). exact Hb.
    + destruct (place_of_pos p tl) eqn:Hrec; try discriminate.
      inversion H. subst i.
      simpl. apply IH. exact Hrec.
Qed.

Lemma place_of_pos_complete :
  forall n (regs : Vector.t Interval n) p i,
    chain_order regs ->
    in_interval p (Vector.nth regs i) ->
    place_of_pos p regs = Some i.
Proof.
  induction regs as [|Iv m tl IH]; intros p i Hord Hin.
  - inversion i.
  - dependent destruction i.
    + simpl.
      assert (in_intervalb p Iv = true).
      { apply (proj2 (in_intervalb_spec _ _)). exact Hin. }
      now rewrite H.
    + simpl.
      assert (Hsep : hi Iv <= lo (Vector.nth tl i)).
      { apply chain_order_head_before_nth. exact Hord. }
      assert (HnotI : ~ in_interval p Iv).
      { eapply interval_after_excludes; eauto. }
      assert (in_intervalb p Iv = false).
      { destruct (in_intervalb p Iv) eqn:Hb; auto.
        exfalso.
        apply (proj1 (in_intervalb_spec _ _)) in Hb.
        exact (HnotI Hb).
      }
      rewrite H.
      specialize (IH p i (chain_order_tail Hord) Hin).
      now rewrite IH.
Qed.

Theorem unique_place_assignment :
  forall n (regs : Vector.t Interval n) p i j,
    chain_order regs ->
    in_interval p (Vector.nth regs i) ->
    in_interval p (Vector.nth regs j) ->
    i = j.
Proof.
  intros n regs p i j Hord Hi Hj.
  pose proof (place_of_pos_complete (regs:=regs) (p:=p) (i:=i) Hord Hi) as Hpi.
  pose proof (place_of_pos_complete (regs:=regs) (p:=p) (i:=j) Hord Hj) as Hpj.
  rewrite Hpi in Hpj. inversion Hpj. reflexivity.
Qed.

Theorem regs_covered_unique_place :
  forall n (regs : Vector.t Interval n) p,
    chain_order regs ->
    regs_covered p regs ->
    exists! i : Fin.t n, in_interval p (Vector.nth regs i).
Proof.
  intros n regs p Hord Hcov.
  destruct (regs_covered_exists_index (regs:=regs) (p:=p) Hcov) as [i Hi].
  exists i. split.
  - exact Hi.
  - intros j Hj. symmetry.
    eapply unique_place_assignment; eauto.
Qed.

(* ========================================================================== *)
(*                          CANONICAL DECIMAL DIALECT                          *)
(* ========================================================================== *)

(* The encoding rules below represent the "canonical decimal dialect" first
   described by Locke (1923) and verified across hundreds of specimens by
   the Aschers (1981) and the Harvard Khipu Database Project.

   Example: To encode 731:
     - Units register: 1 figure-eight knot (representing 1)
     - Tens register: 3 overhand knots in a cluster (representing 30)
     - Hundreds register: 7 overhand knots in a cluster (representing 700)

   The units place is distinguished by using figure-eight and long knots,
   which allows multiple numbers to be encoded sequentially on a single
   pendant cord when needed.

   Units (place 0):
     0    => no knot (absence indicates zero)
     1    => exactly one FigureEight
     2..9 => exactly one Long with corresponding turns
   Higher places (>=1):
     d => exactly d Overhand knots (d may be 0). *)

Definition units_ok (ks : list Knot) : Prop :=
  match ks with
  | List.nil => True
  | List.cons k List.nil =>
      match k_kind k with
      | FigureEight => True
      | Long _ => True
      | _ => False
      end
  | _ => False
  end.

Definition higher_ok (ks : list Knot) : Prop :=
  (forall k, List.In k ks -> k_kind k = Overhand) /\
  length ks < 10.

Definition units_okb (ks : list Knot) : bool :=
  match ks with
  | List.nil => true
  | List.cons k List.nil =>
      match k_kind k with
      | FigureEight => true
      | Long _ => true
      | _ => false
      end
  | _ => false
  end.

Definition higher_okb (ks : list Knot) : bool :=
  all_overhandb ks && (length ks <? 10).

Lemma units_okb_spec : forall ks, units_okb ks = true <-> units_ok ks.
Proof.
  intro ks.
  destruct ks as [|a ks'].
  - simpl. tauto.
  - destruct ks' as [|b ks''].
    + simpl. destruct (k_kind a); (split; intro H; try reflexivity; try exact Logic.I; try discriminate; try contradiction).
    + simpl. split; intro H; discriminate + contradiction.
Qed.

Lemma higher_okb_spec : forall ks, higher_okb ks = true <-> higher_ok ks.
Proof.
  intro ks. unfold higher_okb, higher_ok.
  rewrite andb_true_iff.
  rewrite all_overhandb_spec.
  rewrite Nat.ltb_lt.
  tauto.
Qed.

Definition reg_ok (is_units : bool) (ks : list Knot) : Prop :=
  if is_units then units_ok ks else higher_ok ks.

Definition reg_okb (is_units : bool) (ks : list Knot) : bool :=
  if is_units then units_okb ks else higher_okb ks.

Lemma reg_okb_spec : forall b ks,
  reg_okb b ks = true <-> reg_ok b ks.
Proof.
  intros b ks. destruct b; simpl; [apply units_okb_spec|apply higher_okb_spec].
Qed.

(* Placewise constraints over a full register vector: head = units; tail = higher. *)
Fixpoint regs_ok_at {n : nat} (is_units : bool)
  (regs : Vector.t Interval n) (ks : list Knot) : Prop :=
  match regs with
  | [] => True
  | Iv :: tl =>
      reg_ok is_units (knots_in Iv ks) /\
      regs_ok_at false tl ks
  end.

Definition regs_ok {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : Prop :=
  regs_ok_at true regs ks.

Fixpoint regs_okb_at {n : nat} (is_units : bool)
  (regs : Vector.t Interval n) (ks : list Knot) : bool :=
  match regs with
  | [] => true
  | Iv :: tl =>
      reg_okb is_units (knots_in Iv ks) &&
      regs_okb_at false tl ks
  end.

Definition regs_okb {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : bool :=
  regs_okb_at true regs ks.

Lemma regs_okb_at_spec :
  forall n (regs : Vector.t Interval n) ks b,
    regs_okb_at b regs ks = true <-> regs_ok_at b regs ks.
Proof.
  induction regs as [|I n tl IH]; intros ks b; simpl.
  - tauto.
  - rewrite andb_true_iff.
    rewrite reg_okb_spec.
    rewrite IH.
    tauto.
Qed.

Lemma regs_okb_spec :
  forall n (regs : Vector.t Interval n) ks,
    regs_okb regs ks = true <-> regs_ok regs ks.
Proof.
  intros n regs ks. unfold regs_okb, regs_ok. apply regs_okb_at_spec.
Qed.

(* ========================================================================== *)
(*                              WELL-FORMEDNESS                               *)
(* ========================================================================== *)

Definition WellFormed {n : nat} (ns : NumeralSpec n) (ks : list Knot) : Prop :=
  (forall k, List.In k ks -> k_pos k < ns_len ns) /\
  (forall k, List.In k ks -> regs_covered (k_pos k) (ns_regs ns)) /\
  regs_ok (ns_regs ns) ks.

Definition WellFormedb {n : nat} (ns : NumeralSpec n) (ks : list Knot) : bool :=
  let len := ns_len ns in
  let regs := ns_regs ns in
  let in_boundsb :=
    forallb (fun k => k_pos k <? len) ks in
  let coveredb :=
    forallb (fun k => regs_coveredb (k_pos k) regs) ks in
  in_boundsb && coveredb && regs_okb regs ks.

Lemma forallb_pos_lt_spec :
  forall (len : pos) (ks : list Knot),
    forallb (fun k => k_pos k <? len) ks = true <->
    (forall k, List.In k ks -> k_pos k < len).
Proof.
  intros len ks.
  rewrite forallb_forall.
  split.
  - intros H k Hin. specialize (H k Hin).
    now apply Nat.ltb_lt.
  - intros H k Hin. specialize (H k Hin).
    now apply Nat.ltb_lt.
Qed.

Lemma forallb_regs_covered_spec :
  forall n (regs : Vector.t Interval n) (ks : list Knot),
    forallb (fun k => regs_coveredb (k_pos k) regs) ks = true <->
    (forall k, List.In k ks -> regs_covered (k_pos k) regs).
Proof.
  intros n regs ks.
  rewrite forallb_forall.
  split.
  - intros H k Hin. specialize (H k Hin).
    apply (proj1 (regs_coveredb_spec (k_pos k) regs)). exact H.
  - intros H k Hin. specialize (H k Hin).
    apply (proj2 (regs_coveredb_spec (k_pos k) regs)). exact H.
Qed.

Lemma WellFormedb_spec :
  forall n (ns : NumeralSpec n) ks,
    WellFormedb ns ks = true <-> WellFormed ns ks.
Proof.
  intros n ns ks.
  unfold WellFormedb, WellFormed.
  set (len := ns_len ns).
  set (regs := ns_regs ns).
  repeat rewrite andb_true_iff.
  rewrite forallb_pos_lt_spec.
  rewrite forallb_regs_covered_spec.
  rewrite regs_okb_spec.
  tauto.
Qed.

Theorem WellFormed_decidable :
  forall n (ns : NumeralSpec n) ks,
    {WellFormed ns ks} + {~ WellFormed ns ks}.
Proof.
  intros n ns ks.
  destruct (WellFormedb ns ks) eqn:Hb.
  - left. apply (proj1 (WellFormedb_spec ns ks)). exact Hb.
  - right. intro WF.
    apply (proj2 (WellFormedb_spec ns ks)) in WF.
    congruence.
Qed.

(* ========================================================================== *)
(*                              DECODING REGISTERS                             *)
(* ========================================================================== *)

Definition decode_units (ks : list Knot) : option digit :=
  match ks with
  | List.nil => Some digit0
  | List.cons k List.nil =>
      match k_kind k with
      | FigureEight => Some digit1
      | Long t => Some (digit_of_nat (tval t) (turns_lt10 t))
      | _ => None
      end
  | _ => None
  end.

Definition decode_higher (ks : list Knot) : option digit :=
  if all_overhandb ks then
    match lt_dec (length ks) 10 with
    | left Hlt => Some (digit_of_nat (length ks) Hlt)
    | right _ => None
    end
  else None.

Definition decode_reg (is_units : bool) (ks : list Knot) : option digit :=
  if is_units then decode_units ks else decode_higher ks.

Lemma decode_units_total_if_ok : forall ks,
  units_ok ks -> exists d, decode_units ks = Some d.
Proof.
  intros ks Hok.
  destruct ks as [|a ks'].
  - simpl. eauto.
  - destruct ks' as [|b ks''].
    + simpl. simpl in Hok. destruct (k_kind a); try contradiction; eauto.
    + simpl in Hok. contradiction.
Qed.

Lemma decode_higher_total_if_ok : forall ks,
  higher_ok ks -> exists d, decode_higher ks = Some d.
Proof.
  intros ks [Hall Hlen].
  unfold decode_higher.
  assert (all_overhandb ks = true).
  { apply (proj2 (all_overhandb_spec ks)). exact Hall. }
  rewrite H.
  destruct (lt_dec (length ks) 10); eauto; lia.
Qed.

Lemma decode_reg_total_if_ok : forall b ks,
  reg_ok b ks -> exists d, decode_reg b ks = Some d.
Proof.
  intros b ks Hok. destruct b; simpl in *.
  - apply decode_units_total_if_ok. exact Hok.
  - apply decode_higher_total_if_ok. exact Hok.
Qed.

Fixpoint decode_regs_at {n : nat} (is_units : bool)
  (regs : Vector.t Interval n) (ks : list Knot)
  : option (Vector.t digit n) :=
  match regs with
  | [] => Some []
  | Iv :: tl =>
      match decode_reg is_units (knots_in Iv ks),
            decode_regs_at false tl ks with
      | Some d, Some ds => Some (d :: ds)
      | _, _ => None
      end
  end.

Definition decode_regs {n : nat} (regs : Vector.t Interval n) (ks : list Knot)
  : option (Vector.t digit n) :=
  decode_regs_at true regs ks.

Definition outside_all {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : Prop :=
  forall (i : Fin.t n) k, List.In k ks -> ~ in_interval (k_pos k) (Vector.nth regs i).

Lemma outside_all_tail_cons :
  forall n (Iv : Interval) (tl : Vector.t Interval n) ks,
    outside_all (Iv :: tl) ks ->
    outside_all tl ks.
Proof.
  intros n Iv tl ks Hout i k Hin.
  specialize (Hout (Fin.FS i) k Hin). simpl in Hout. exact Hout.
Qed.

Lemma outside_interval_head_cons :
  forall n (Iv : Interval) (tl : Vector.t Interval n) ks,
    outside_all (Iv :: tl) ks ->
    outside_interval Iv ks.
Proof.
  intros n Iv tl ks Hout k Hin.
  specialize (Hout Fin.F1 k Hin). simpl in Hout. exact Hout.
Qed.

Lemma decode_regs_at_app_left_outside_all :
  forall n (regs : Vector.t Interval n) ks1 ks2 b,
    outside_all regs ks1 ->
    decode_regs_at b regs (List.app ks1 ks2) = decode_regs_at b regs ks2.
Proof.
  induction regs as [|Iv m tl IH]; intros ks1 ks2 b Hout; simpl.
  - reflexivity.
  - assert (HoutI : outside_interval Iv ks1).
    { eapply outside_interval_head_cons. exact Hout. }
    assert (HoutTl : outside_all tl ks1).
    { eapply outside_all_tail_cons. exact Hout. }
    rewrite knots_in_app_left_outside_interval; [|exact HoutI].
    rewrite IH; [|exact HoutTl].
    reflexivity.
Qed.

Lemma decode_regs_at_total :
  forall n (regs : Vector.t Interval n) ks b,
    regs_ok_at b regs ks ->
    exists ds, decode_regs_at b regs ks = Some ds.
Proof.
  induction regs as [|Iv m tl IH]; intros ks b Hok; simpl.
  - exists []. reflexivity.
  - destruct Hok as [HokI HokTl].
    destruct (decode_reg_total_if_ok HokI) as [d Hd].
    destruct (IH ks false HokTl) as [ds Hds].
    rewrite Hd, Hds.
    exists (d :: ds). reflexivity.
Qed.

Theorem decode_total_under_WF :
  forall n (ns : NumeralSpec n) ks,
    WellFormed ns ks ->
    exists ds, decode_regs (ns_regs ns) ks = Some ds.
Proof.
  intros n ns ks [_ [_ Hok]].
  unfold decode_regs.
  apply (decode_regs_at_total (regs:=ns_regs ns) (ks:=ks) (b:=true)).
  exact Hok.
Qed.

(* ========================================================================== *)
(*                           NUMERIC SEMANTICS OF DIGITS                       *)
(* ========================================================================== *)

Fixpoint value_digits {n : nat} (ds : Vector.t digit n) : nat :=
  match ds with
  | [] => 0
  | d :: tl => digit_to_nat d + 10 * value_digits tl
  end.

(* ========================================================================== *)
(*                         CANONICAL ENCODING (CONSTRUCTIVE)                   *)
(* ========================================================================== *)

Definition mk_overhand (p : pos) : Knot :=
  {| k_pos := p; k_kind := Overhand; k_twist := TZ |}.

Definition mk_fig8 (p : pos) : Knot :=
  {| k_pos := p; k_kind := FigureEight; k_twist := TZ |}.

Definition mk_long (p : pos) (n : nat) (H : 2 <= n <= 9) : Knot :=
  {| k_pos := p;
     k_kind := Long {| tval := n; t_range := H |};
     k_twist := TZ |}.

Fixpoint overhand_cluster (I : Interval) (n : nat) : list Knot :=
  match n with
  | 0 => []
  | S m => overhand_cluster I m ++ [mk_overhand (slot I m)]
  end.

Lemma overhand_cluster_length : forall I n,
  length (overhand_cluster I n) = n.
Proof.
  intros I n. induction n; simpl.
  - reflexivity.
  - rewrite app_length. simpl. lia.
Qed.

Lemma overhand_cluster_all_overhand : forall Iv n k,
  List.In k (overhand_cluster Iv n) -> k_kind k = Overhand.
Proof.
  intros Iv n. induction n; simpl; intros k Hin.
  - contradiction.
  - apply in_app_or in Hin as [Hin|Hin].
    + apply IHn; exact Hin.
    + simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
      subst k. reflexivity.
Qed.

Lemma overhand_cluster_positions_in_Iv :
  forall Iv n k,
    n < 10 ->
    wide_enough Iv ->
    List.In k (overhand_cluster Iv n) ->
    in_interval (k_pos k) Iv.
Proof.
  intros I n. induction n; simpl; intros k Hn Hwide Hin.
  - contradiction.
  - apply in_app_or in Hin as [Hin|Hin].
    + apply IHn; try lia; auto.
    + simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
      subst k. simpl.
      apply slot_in_interval; try lia; auto.
Qed.

Definition make_turns (n : nat) (H : 2 <= n /\ n <= 9) : Turns :=
  {| tval := n; t_range := H |}.

Lemma encode_units_aux2 : forall m, S (S m) < 10 -> 2 <= S (S m) <= 9.
Proof. intros. lia. Qed.
Arguments encode_units_aux2 m H : clear implicits.

Definition encode_units (Iv : Interval) (d : digit) : list Knot :=
  let n := digit_to_nat d in
  let Hlt := digit_to_nat_lt10 d in
  match n as n' return (n' < 10 -> list Knot) with
  | 0 => fun _ => @List.nil Knot
  | 1 => fun _ => List.cons (mk_fig8 (slot Iv 0)) (@List.nil Knot)
  | S (S m) => fun H => List.cons (@mk_long (slot Iv 0) (S (S m)) (encode_units_aux2 m H)) (@List.nil Knot)
  end Hlt.

Definition encode_higher (Iv : Interval) (d : digit) : list Knot :=
  overhand_cluster Iv (digit_to_nat d).

Definition encode_reg (is_units : bool) (Iv : Interval) (d : digit) : list Knot :=
  if is_units then encode_units Iv d else encode_higher Iv d.

Fixpoint encode_regs_at {n : nat} (is_units : bool)
  (regs : Vector.t Interval n) : Vector.t digit n -> list Knot :=
  match regs with
  | [] => fun _ => @List.nil Knot
  | Iv :: tlI => fun ds =>
      List.app (encode_reg is_units Iv (Vector.hd ds)) (encode_regs_at false tlI (Vector.tl ds))
  end.

Definition encode_regs {n : nat} (regs : Vector.t Interval n) (ds : Vector.t digit n) : list Knot :=
  encode_regs_at true regs ds.

Definition encode {n : nat} (ns : NumeralSpec n) (ds : Vector.t digit n) : list Knot :=
  encode_regs (ns_regs ns) ds.

Lemma encode_units_ok : forall Iv d, units_ok (encode_units Iv d).
Proof.
  intros Iv d.
  unfold encode_units.
  generalize (digit_to_nat_lt10 d).
  generalize (digit_to_nat d) at 1 2.
  intros n Hlt.
  destruct n as [|[|m]]; simpl; auto.
Qed.

Lemma encode_higher_ok : forall Iv d, higher_ok (encode_higher Iv d).
Proof.
  intros Iv d. unfold encode_higher, higher_ok.
  split.
  - intros k Hin. apply overhand_cluster_all_overhand in Hin. exact Hin.
  - rewrite overhand_cluster_length.
    apply digit_to_nat_lt10.
Qed.

Lemma encode_reg_ok : forall b Iv d, reg_ok b (encode_reg b Iv d).
Proof.
  intros b Iv d. destruct b; simpl.
  - apply encode_units_ok.
  - apply encode_higher_ok.
Qed.

Lemma encode_units_positions_in_Iv :
  forall Iv d k,
    wide_enough Iv ->
    List.In k (encode_units Iv d) ->
    in_interval (k_pos k) Iv.
Proof.
  intros Iv d k Hwide.
  unfold encode_units.
  generalize (digit_to_nat_lt10 d).
  generalize (digit_to_nat d) at 1 2.
  intros n Hlt.
  destruct n as [|[|m]]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hin|Hin]; [|contradiction]. subst k. simpl.
    apply slot_in_interval; auto; lia.
  - destruct Hin as [Hin|Hin]; [|contradiction]. subst k. simpl.
    apply slot_in_interval; auto; lia.
Qed.

Lemma encode_higher_positions_in_Iv :
  forall Iv d k,
    wide_enough Iv ->
    List.In k (encode_higher Iv d) ->
    in_interval (k_pos k) Iv.
Proof.
  intros Iv d k Hwide Hin.
  unfold encode_higher in Hin.
  apply (@overhand_cluster_positions_in_Iv Iv (digit_to_nat d) k (digit_to_nat_lt10 d) Hwide Hin).
Qed.

Lemma encode_reg_positions_in_Iv :
  forall b Iv d k,
    wide_enough Iv ->
    List.In k (encode_reg b Iv d) ->
    in_interval (k_pos k) Iv.
Proof.
  intros b Iv d k Hwide Hin.
  destruct b; simpl in *.
  - eapply encode_units_positions_in_Iv; eauto.
  - eapply encode_higher_positions_in_Iv; eauto.
Qed.

Lemma encode_regs_at_member_index :
  forall n (regs : Vector.t Interval n) (ds : Vector.t digit n) b k,
    all_wide regs ->
    List.In k (encode_regs_at b regs ds) ->
    exists i : Fin.t n, in_interval (k_pos k) (Vector.nth regs i).
Proof.
  induction regs as [|Iv m tl IH]; intros ds b k Hwide Hin.
  - dependent destruction ds. simpl in Hin. contradiction.
  - dependent destruction ds.
    simpl in Hwide. destruct Hwide as [HwideI HwideTl].
    simpl in Hin. apply in_app_or in Hin as [HinH|HinT].
    + exists Fin.F1. simpl.
      eapply encode_reg_positions_in_Iv; eauto.
    + destruct (IH ds false k HwideTl HinT) as [i Hi].
      exists (Fin.FS i). simpl. exact Hi.
Qed.

Lemma encode_regs_at_outside_interval_head :
  forall n (Iv : Interval) (tl : Vector.t Interval n) (ds : Vector.t digit n) k,
    all_wide tl ->
    chain_order (Iv :: tl) ->
    List.In k (encode_regs_at false tl ds) ->
    ~ in_interval (k_pos k) Iv.
Proof.
  intros n Iv tl ds k HwideTl Hord Hin.
  destruct (encode_regs_at_member_index HwideTl Hin) as [i Hi].
  pose proof (chain_order_head_before_nth i Hord) as Hsep.
  eapply interval_after_excludes; eauto.
Qed.

Lemma encode_reg_outside_all_tail :
  forall n (Iv : Interval) (tl : Vector.t Interval n) b d,
    chain_order (Iv :: tl) ->
    wide_enough Iv ->
    outside_all tl (encode_reg b Iv d).
Proof.
  intros n Iv tl b d Hord Hwide i k Hin.
  pose proof (encode_reg_positions_in_Iv Hwide Hin) as HinI.
  pose proof (chain_order_head_before_nth i Hord) as Hsep.
  eapply interval_before_excludes; eauto.
Qed.

Lemma regs_ok_at_app_left_outside_all :
  forall n (regs : Vector.t Interval n) ks1 ks2 b,
    outside_all regs ks1 ->
    regs_ok_at b regs (List.app ks1 ks2) <-> regs_ok_at b regs ks2.
Proof.
  induction regs as [|Iv m tl IH]; intros ks1 ks2 b Hout; simpl.
  - tauto.
  - assert (HoutI : outside_interval Iv ks1).
    { eapply outside_interval_head_cons. exact Hout. }
    assert (HoutTl : outside_all tl ks1).
    { eapply outside_all_tail_cons. exact Hout. }
    rewrite (@knots_in_app_left_outside_interval Iv ks1 ks2 HoutI).
    split.
    + intros [Hhead Htail]. split; [exact Hhead|].
      apply (proj1 (IH ks1 ks2 false HoutTl)). exact Htail.
    + intros [Hhead Htail]. split; [exact Hhead|].
      apply (proj2 (IH ks1 ks2 false HoutTl)). exact Htail.
Qed.

Lemma encode_regs_ok_at :
  forall n (regs : Vector.t Interval n) (ds : Vector.t digit n) b,
    all_wide regs ->
    chain_order regs ->
    regs_ok_at b regs (encode_regs_at b regs ds).
Proof.
  induction regs as [|Iv m tl IH]; intros ds b Hwide Hord; simpl.
  - dependent destruction ds. simpl. exact Logic.I.
  - dependent destruction ds.
    simpl in Hwide. destruct Hwide as [HwideI HwideTl].
    split.
    + assert (Hkh : knots_in Iv (encode_reg b Iv h) = encode_reg b Iv h).
      { apply knots_in_self.
        intros k Hin.
        eapply encode_reg_positions_in_Iv; eauto.
      }
      assert (Hkt : knots_in Iv (encode_regs_at false tl ds) = @List.nil Knot).
      { apply knots_in_none.
        intros k Hin.
        eapply encode_regs_at_outside_interval_head.
        - exact HwideTl.
        - exact Hord.
        - exact Hin.
      }
      simpl.
      rewrite knots_in_app, Hkh, Hkt.
      rewrite List.app_nil_r.
      apply encode_reg_ok.
    + assert (Hout : outside_all tl (encode_reg b Iv h)).
      { apply encode_reg_outside_all_tail; auto. }
      simpl.
      apply (proj2 (@regs_ok_at_app_left_outside_all m tl (encode_reg b Iv h) (encode_regs_at false tl ds) false Hout)).
      apply IH.
        -- exact HwideTl.
        -- exact (chain_order_tail Hord).
Qed.

Lemma in_interval_nth_implies_covered :
  forall n (regs : Vector.t Interval n) (i : Fin.t n) p,
    in_interval p (Vector.nth regs i) ->
    regs_covered p regs.
Proof.
  induction regs as [|Iv m tl IH]; intros i p Hi.
  - inversion i.
  - dependent destruction i; simpl in *.
    + left. exact Hi.
    + right. apply (IH i p Hi).
Defined.

Theorem encode_is_WellFormed :
  forall n (ns : NumeralSpec n) ds,
    WellFormed ns (encode ns ds).
Proof.
  intros n ns ds.
  unfold WellFormed, encode.
  set (regs := ns_regs ns).
  set (len := ns_len ns).
  set (ks := encode_regs regs ds).
  split.
  - (* bounds *)
    intros k Hin.
    destruct (encode_regs_at_member_index (regs:=regs) (ds:=ds) (b:=true) (k:=k) (ns_wide ns) Hin)
      as [i Hi].
    pose proof (@all_within_nth len n regs i (ns_within ns)) as Hhi.
    destruct Hi as [_ Hlt]. lia.
  - split.
    + (* coverage *)
      intros k Hin.
      destruct (encode_regs_at_member_index (regs:=regs) (ds:=ds) (b:=true) (k:=k) (ns_wide ns) Hin)
        as [i Hi].
      apply (in_interval_nth_implies_covered (regs:=regs) (i:=i) (p:=k_pos k) Hi).
    + (* per-register dialect *)
      unfold ks.
      unfold encode_regs.
      apply encode_regs_ok_at.
      * exact (ns_wide ns).
      * exact (ns_order ns).
Qed.

(* ========================================================================== *)
(*                        DECODE(ENCODE(ds)) = ds                               *)
(* ========================================================================== *)

Lemma lt_unique : forall m n (h1 h2 : m < n), h1 = h2.
Proof.
  intros m n h1 h2.
  apply Peano_dec.le_unique.
Qed.

Lemma decode_units_encode_units_aux :
  forall I n (Hlt : n < 10),
    decode_units
      (match n as n' return (n' < 10 -> list Knot) with
       | 0 => fun _ => @List.nil Knot
       | 1 => fun _ => List.cons (mk_fig8 (slot I 0)) List.nil
       | S (S m) => fun H => List.cons (mk_long (slot I 0) (encode_units_aux2 m H)) List.nil
       end Hlt) = Some (digit_of_nat n Hlt).
Proof.
  intros I n Hlt.
  destruct n as [|[|k]]; simpl; f_equal; apply digit_ext;
    unfold digit0, digit1; rewrite ?digit_to_nat_of_nat_lt; reflexivity.
Qed.

Lemma decode_units_encode_units :
  forall I d,
    decode_units (encode_units I d) = Some d.
Proof.
  intros I d.
  unfold encode_units.
  rewrite decode_units_encode_units_aux.
  f_equal.
  apply digit_of_nat_to_nat.
Qed.

Lemma decode_higher_encode_higher :
  forall I d,
    decode_higher (encode_higher I d) = Some d.
Proof.
  intros I d.
  unfold decode_higher, encode_higher.
  assert (all_overhandb (overhand_cluster I (digit_to_nat d)) = true).
  { apply (proj2 (all_overhandb_spec _)).
    intros k Hin. apply overhand_cluster_all_overhand in Hin. exact Hin. }
  rewrite H.
  destruct (lt_dec (length (overhand_cluster I (digit_to_nat d))) 10) as [Hlt|Hge].
  - f_equal.
    apply digit_ext.
    rewrite digit_to_nat_of_nat_lt.
    apply overhand_cluster_length.
  - exfalso.
    rewrite overhand_cluster_length in Hge.
    pose proof (digit_to_nat_lt10 d). lia.
Qed.

Lemma decode_reg_encode_reg :
  forall b I d,
    decode_reg b (encode_reg b I d) = Some d.
Proof.
  intros b I d. destruct b; simpl.
  - apply decode_units_encode_units.
  - apply decode_higher_encode_higher.
Qed.

Theorem decode_encode_roundtrip_at :
  forall n (regs : Vector.t Interval n) ds b,
    all_wide regs ->
    chain_order regs ->
    decode_regs_at b regs (encode_regs_at b regs ds) = Some ds.
Proof.
  induction regs as [|I n tl IH]; intros ds b Hwide Hord; simpl.
  - dependent destruction ds. reflexivity.
  - dependent destruction ds.
    simpl in Hwide. destruct Hwide as [HwideI HwideTl].
    assert (Hkh : knots_in I (encode_reg b I h) = encode_reg b I h).
    { apply knots_in_self.
      intros k Hin.
      eapply encode_reg_positions_in_Iv; eauto.
    }
    assert (Hkt : knots_in I (encode_regs_at false tl ds) = @List.nil Knot).
    { apply knots_in_none.
      intros k Hin.
      eapply encode_regs_at_outside_interval_head; eauto.
    }
    simpl.
    rewrite knots_in_app, Hkh, Hkt, List.app_nil_r.
    assert (Hout : outside_all tl (encode_reg b I h)).
    { apply encode_reg_outside_all_tail; auto. }
    rewrite (@decode_regs_at_app_left_outside_all n tl (encode_reg b I h) (encode_regs_at false tl ds) false Hout).
    rewrite (IH ds false HwideTl (chain_order_tail (Iv:=I) (tl:=tl) Hord)).
    rewrite decode_reg_encode_reg.
    reflexivity.
Qed.

Theorem decode_encode_roundtrip :
  forall n (ns : NumeralSpec n) ds,
    decode_regs (ns_regs ns) (encode ns ds) = Some ds.
Proof.
  intros n ns ds.
  unfold decode_regs, encode.
  apply decode_encode_roundtrip_at.
  - exact (ns_wide ns).
  - exact (ns_order ns).
Qed.

Corollary value_preserved_by_roundtrip :
  forall n (ns : NumeralSpec n) ds,
    exists ds', decode_regs (ns_regs ns) (encode ns ds) = Some ds' /\
                value_digits ds' = value_digits ds.
Proof.
  intros n ns ds.
  exists ds. split.
  - apply decode_encode_roundtrip.
  - reflexivity.
Qed.

(* ========================================================================== *)
(*                             FIELD READING API                               *)
(* ========================================================================== *)

Definition place_of_knot {n : nat} (ns : NumeralSpec n) (k : Knot) : option (Fin.t n) :=
  place_of_pos (k_pos k) (ns_regs ns).

Definition decode_checked {n : nat} (ns : NumeralSpec n) (ks : list Knot)
  : option (Vector.t digit n) :=
  if WellFormedb ns ks then decode_regs (ns_regs ns) ks else None.

Definition value_checked {n : nat} (ns : NumeralSpec n) (ks : list Knot) : option nat :=
  option_map value_digits (decode_checked ns ks).

Lemma decode_checked_total_under_WF :
  forall n (ns : NumeralSpec n) ks,
    WellFormed ns ks ->
    exists ds, decode_checked ns ks = Some ds.
Proof.
  intros n ns ks Hwf.
  unfold decode_checked.
  assert (WellFormedb ns ks = true).
  { apply (proj2 (WellFormedb_spec ns ks)). exact Hwf. }
  rewrite H.
  destruct (decode_total_under_WF (ns:=ns) (ks:=ks) Hwf) as [ds Hds].
  exists ds. exact Hds.
Qed.

(* ========================================================================== *)
(*                        MULTI-NUMBER PENDANT CORDS                          *)
(* ========================================================================== *)

(* Because figure-eight and long knots only appear in the units position,
   khipu makers could encode multiple numbers sequentially on a single
   pendant cord. When a figure-eight or long knot is encountered, it marks
   the end of one number; the next cluster of overhand knots above begins
   a new number.

   For example, the sequence "107, 51" on one cord would be:
     1 overhand (hundreds), 0 (gap), 7-turn long knot (units of first number),
     5 overhand (tens), 1 figure-eight (units of second number).

   This feature was noted by Locke (1923) and is well-attested in the
   archaeological record for census and accounting khipu. *)

Definition MultiNumeral (n : nat) : Type := list (Vector.t digit n).

Definition multi_value {n : nat} (mn : MultiNumeral n) : list nat :=
  List.map value_digits mn.

(* ========================================================================== *)
(*                         EXTENSION: FULL KHIPU TREES                          *)
(* ========================================================================== *)

(* Khipu cords were made from either cotton (Gossypium barbadense) grown on
   the coast, or camelid fiber (llama, alpaca, vicuña) from the highlands.
   The Aschers (1981) noted that fiber choice may correlate with regional
   origin or administrative context. *)

Inductive Fiber : Type :=
| Cotton
| Camelid.

(* Color encoding remains incompletely deciphered, but the Aschers (1981)
   and the Harvard Khipu Database Project documented recurring color
   categories. Colors likely encoded categorical information such as
   commodity types, social groups, or administrative units. Some khipu
   show mottled or "barber-pole" striped cords created by plying threads
   of different colors together. *)

Inductive Color : Type :=
| White
| LightBrown
| MediumBrown
| DarkBrown
| Black
| Red
| Yellow
| Green
| Blue
| Grey
| Mottled (c1 c2 : Color).

Record CordMeta : Type := {
  cm_fiber : Fiber;
  cm_color : Color;
  cm_spin  : Twist;
  cm_ply   : Twist
}.

(* Pendant cords attach to the primary cord in one of two orientations:
   Recto (toward the viewer) or Verso (away from the viewer). The Harvard
   Khipu Database records this as a binary feature that may carry encoded
   meaning, though its semantics remain undeciphered. *)

Inductive AttachDir : Type :=
| Recto
| Verso.

Inductive Cord : Type :=
| CordNode : CordMeta -> pos -> list Knot -> list Attachment -> Cord
with Attachment : Type :=
| Attach : AttachDir -> pos -> Cord -> Attachment.

Definition cord_len (c : Cord) : pos :=
  match c with CordNode _ L _ _ => L end.

Definition cord_knots (c : Cord) : list Knot :=
  match c with CordNode _ _ ks _ => ks end.

Definition cord_children (c : Cord) : list Attachment :=
  match c with CordNode _ _ _ ch => ch end.

Record NumericPendant (n : nat) : Type := {
  np_meta  : CordMeta;
  np_spec  : NumeralSpec n;
  np_knots : list Knot;
  np_wf    : WellFormed np_spec np_knots
}.

Definition pendant_digits {n} (p : NumericPendant n) : option (Vector.t digit n) :=
  decode_checked (np_spec p) (np_knots p).

Definition pendant_value {n} (p : NumericPendant n) : option nat :=
  option_map value_digits (pendant_digits p).

Definition Ledger : Type := list { n : nat & NumericPendant n }.

Fixpoint ledger_values (L : Ledger) : list (option nat) :=
  match L with
  | List.nil => List.nil
  | List.cons (existT _ n p) tl => List.cons (pendant_value p) (ledger_values tl)
  end.

Definition attachment_within (parent_len : pos) (a : Attachment) : Prop :=
  match a with
  | Attach _ p child => p < parent_len /\ cord_len child > 0
  end.

Inductive cord_wf : Cord -> Prop :=
| cord_wf_node : forall m L ks ch,
    0 < L ->
    (forall k, List.In k ks -> k_pos k < L) ->
    attachments_wf L ch ->
    cord_wf (CordNode m L ks ch)
with attachments_wf : pos -> list Attachment -> Prop :=
| attachments_wf_nil : forall L, attachments_wf L List.nil
| attachments_wf_cons : forall L dir p child tl,
    p < L ->
    cord_len child > 0 ->
    cord_wf child ->
    attachments_wf L tl ->
    attachments_wf L (List.cons (Attach dir p child) tl).

(* ========================================================================== *)
(*                           TOP CORD SUMMATION                               *)
(* ========================================================================== *)

(* A distinctive structural feature of administrative khipu is the presence
   of "top cords" that extend upward from the primary cord. Locke (1923)
   and the Aschers (1981) observed that top cord values frequently equal
   the sum of adjacent pendant cord values. A 2024 computational study
   confirmed this pattern in 74% of khipu exhibiting internal sums.

   This summation property likely served as an error-checking mechanism
   and facilitated hierarchical aggregation of accounting data. *)

(* A pendant group consists of a top cord and the pendant cords it summarizes. *)
Record PendantGroup (n : nat) : Type := {
  pg_top      : NumericPendant n;
  pg_pendants : list (NumericPendant n)
}.

(* The summation invariant: top cord value equals sum of pendant values. *)
Definition group_sums_valid {n : nat} (g : PendantGroup n) : Prop :=
  match pendant_value (pg_top g) with
  | None => False
  | Some top_val =>
      let pendant_vals := List.map pendant_value (pg_pendants g) in
      let sum_opt := List.fold_right
        (fun ov acc =>
          match ov, acc with
          | Some v, Some a => Some (v + a)
          | _, _ => None
          end)
        (Some 0)
        pendant_vals in
      match sum_opt with
      | Some s => top_val = s
      | None => False
      end
  end.

Definition group_sums_validb {n : nat} (g : PendantGroup n) : bool :=
  match pendant_value (pg_top g) with
  | None => false
  | Some top_val =>
      let pendant_vals := List.map pendant_value (pg_pendants g) in
      let sum_opt := List.fold_right
        (fun ov acc =>
          match ov, acc with
          | Some v, Some a => Some (v + a)
          | _, _ => None
          end)
        (Some 0)
        pendant_vals in
      match sum_opt with
      | Some s => top_val =? s
      | None => false
      end
  end.

Lemma group_sums_validb_spec :
  forall n (g : PendantGroup n),
    group_sums_validb g = true <-> group_sums_valid g.
Proof.
  intros n g.
  unfold group_sums_validb, group_sums_valid.
  destruct (pendant_value (pg_top g)) as [top_val|].
  - set (pendant_vals := List.map pendant_value (pg_pendants g)).
    set (sum_opt := List.fold_right _ _ _).
    destruct sum_opt as [s|].
    + rewrite Nat.eqb_eq. tauto.
    + split; intro H; discriminate + contradiction.
  - split; intro H; discriminate + contradiction.
Qed.

Theorem group_sums_valid_decidable :
  forall n (g : PendantGroup n),
    {group_sums_valid g} + {~ group_sums_valid g}.
Proof.
  intros n g.
  destruct (group_sums_validb g) eqn:Hb.
  - left. apply (proj1 (group_sums_validb_spec g)). exact Hb.
  - right. intro Hv.
    apply (proj2 (group_sums_validb_spec g)) in Hv.
    congruence.
Qed.

(* ========================================================================== *)
(*                        SUBSIDIARY CORD DEPTH                               *)
(* ========================================================================== *)

(* Archaeological studies have documented subsidiary cord structures up to
   12 levels deep. We define a depth-bounded well-formedness predicate to
   capture this constraint. The depth parameter tracks remaining allowed
   nesting levels.

   We use an inductive predicate with an explicit depth bound rather than
   a fixpoint to avoid termination issues with the mutually-recursive
   cord/attachment structure. *)

Inductive cord_wf_depth : nat -> Cord -> Prop :=
| cord_wf_depth_node : forall fuel m L ks ch,
    0 < L ->
    (forall k, List.In k ks -> k_pos k < L) ->
    attachments_wf_depth fuel L ch ->
    cord_wf_depth (S fuel) (CordNode m L ks ch)
with attachments_wf_depth : nat -> pos -> list Attachment -> Prop :=
| attachments_wf_depth_nil : forall fuel L,
    attachments_wf_depth fuel L List.nil
| attachments_wf_depth_cons : forall fuel L dir p child tl,
    p < L ->
    cord_len child > 0 ->
    cord_wf_depth fuel child ->
    attachments_wf_depth fuel L tl ->
    attachments_wf_depth fuel L (List.cons (Attach dir p child) tl).

Definition max_subsidiary_depth : nat := 12.

Definition cord_wf_bounded (c : Cord) : Prop :=
  cord_wf_depth (S max_subsidiary_depth) c.

Lemma cord_wf_depth_positive :
  forall n c, cord_wf_depth n c -> 0 < n.
Proof.
  intros n c H. destruct H. lia.
Qed.

(* ========================================================================== *)
(*                         COMPUTATIONAL EXAMPLES                             *)
(* ========================================================================== *)

(* We provide concrete examples demonstrating the encoding system. These
   examples can be extracted to OCaml for computational verification. *)

Section Examples.

Lemma lt_2_10 : 2 < 10. Proof. lia. Qed.
Lemma lt_3_10 : 3 < 10. Proof. lia. Qed.
Lemma lt_4_10 : 4 < 10. Proof. lia. Qed.
Lemma lt_5_10 : 5 < 10. Proof. lia. Qed.
Lemma lt_6_10 : 6 < 10. Proof. lia. Qed.
Lemma lt_7_10 : 7 < 10. Proof. lia. Qed.
Lemma lt_8_10 : 8 < 10. Proof. lia. Qed.
Lemma lt_9_10 : 9 < 10. Proof. lia. Qed.

Definition digit2 : digit := digit_of_nat 2 lt_2_10.
Definition digit3 : digit := digit_of_nat 3 lt_3_10.
Definition digit4 : digit := digit_of_nat 4 lt_4_10.
Definition digit5 : digit := digit_of_nat 5 lt_5_10.
Definition digit6 : digit := digit_of_nat 6 lt_6_10.
Definition digit7 : digit := digit_of_nat 7 lt_7_10.
Definition digit8 : digit := digit_of_nat 8 lt_8_10.
Definition digit9 : digit := digit_of_nat 9 lt_9_10.

Lemma interval_0_12_ok : 0 < 12. Proof. lia. Qed.
Lemma interval_12_24_ok : 12 < 24. Proof. lia. Qed.
Lemma interval_24_36_ok : 24 < 36. Proof. lia. Qed.

Definition units_interval : Interval :=
  {| lo := 0; hi := 12; lo_lt_hi := interval_0_12_ok |}.

Definition tens_interval : Interval :=
  {| lo := 12; hi := 24; lo_lt_hi := interval_12_24_ok |}.

Definition hundreds_interval : Interval :=
  {| lo := 24; hi := 36; lo_lt_hi := interval_24_36_ok |}.

Definition example_regs : Vector.t Interval 3 :=
  [units_interval; tens_interval; hundreds_interval].

Lemma example_chain_order : chain_order example_regs.
Proof.
  unfold example_regs. simpl.
  split; [lia|].
  split; [lia|].
  exact I.
Qed.

Lemma example_all_wide : all_wide example_regs.
Proof.
  unfold example_regs. simpl.
  unfold wide_enough. simpl.
  repeat split; lia.
Qed.

Lemma example_all_within : all_within 36 example_regs.
Proof.
  unfold example_regs. simpl.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  exact I.
Qed.

Lemma example_len_pos : 0 < 36. Proof. lia. Qed.

Definition example_spec : NumeralSpec 3 := {|
  ns_len := 36;
  ns_len_pos := example_len_pos;
  ns_regs := example_regs;
  ns_order := example_chain_order;
  ns_wide := example_all_wide;
  ns_within := example_all_within
|}.

Definition digits_731 : Vector.t digit 3 := [digit1; digit3; digit7].

Definition knots_731 : list Knot := encode example_spec digits_731.

Lemma knots_731_wellformed : WellFormed example_spec knots_731.
Proof.
  unfold knots_731.
  apply encode_is_WellFormed.
Qed.

Lemma decode_731_correct :
  decode_regs example_regs knots_731 = Some digits_731.
Proof.
  unfold knots_731, example_regs.
  change (decode_regs (ns_regs example_spec) (encode example_spec digits_731) = Some digits_731).
  apply decode_encode_roundtrip.
Qed.

Lemma value_731_correct : value_digits digits_731 = 731.
Proof.
  unfold digits_731, value_digits, digit_to_nat, digit1, digit3, digit7.
  unfold digit_of_nat. simpl.
  reflexivity.
Qed.

Definition digits_804 : Vector.t digit 3 := [digit4; digit0; digit8].

Definition knots_804 : list Knot := encode example_spec digits_804.

Lemma value_804_correct : value_digits digits_804 = 804.
Proof.
  unfold digits_804, value_digits, digit_to_nat, digit0, digit4, digit8.
  unfold digit_of_nat. simpl.
  reflexivity.
Qed.

Lemma decode_804_correct :
  decode_regs example_regs knots_804 = Some digits_804.
Proof.
  unfold knots_804, example_regs.
  change (decode_regs (ns_regs example_spec) (encode example_spec digits_804) = Some digits_804).
  apply decode_encode_roundtrip.
Qed.

Definition digits_000 : Vector.t digit 3 := [digit0; digit0; digit0].

Definition knots_000 : list Knot := encode example_spec digits_000.

Lemma knots_000_is_empty : knots_000 = @List.nil Knot.
Proof.
  unfold knots_000, encode, encode_regs, encode_regs_at.
  unfold encode_reg, encode_units, encode_higher.
  unfold digit_to_nat, digit0, digit_of_nat.
  simpl. reflexivity.
Qed.

Lemma value_000_correct : value_digits digits_000 = 0.
Proof.
  reflexivity.
Qed.

End Examples.

(* ========================================================================== *)
(*                            MOIETY SEMANTICS                                *)
(* ========================================================================== *)

(* Hyland (2014) demonstrated that S/Z knot orientation correlates with
   Andean moiety organization. S-twist marks Hanan (upper) division and
   Z-twist marks Urin (lower) division. This binary social classification
   pervaded Inka administrative structure. *)

Inductive Moiety : Type :=
| Hanan
| Urin.

Definition twist_to_moiety (t : Twist) : Moiety :=
  match t with
  | TS => Hanan
  | TZ => Urin
  end.

Definition moiety_to_twist (m : Moiety) : Twist :=
  match m with
  | Hanan => TS
  | Urin => TZ
  end.

Lemma twist_moiety_roundtrip : forall t,
  moiety_to_twist (twist_to_moiety t) = t.
Proof.
  intros []; reflexivity.
Qed.

Lemma moiety_twist_roundtrip : forall m,
  twist_to_moiety (moiety_to_twist m) = m.
Proof.
  intros []; reflexivity.
Qed.

Definition knot_moiety (k : Knot) : Moiety :=
  twist_to_moiety (k_twist k).

Definition cord_moiety (cm : CordMeta) : Moiety :=
  twist_to_moiety (cm_spin cm).

(* Markedness theory: S-ply (Hanan) is unmarked/default, Z-ply (Urin) is
   marked. This asymmetry appears in khipu conventions where S is more
   common and Z signals special status. *)

Definition is_marked (t : Twist) : bool :=
  match t with
  | TS => false
  | TZ => true
  end.

Definition is_unmarked (t : Twist) : bool :=
  negb (is_marked t).

Lemma marked_unmarked_exclusive : forall t,
  is_marked t = negb (is_unmarked t).
Proof.
  intros []; reflexivity.
Qed.

(* ========================================================================== *)
(*                           STRUCTURAL MARKERS                               *)
(* ========================================================================== *)

(* Thompson (2024) and the Cambridge data science study (2024) identified
   special cord types that serve structural rather than numerical functions:
   - Divider cords: red/white cords separating pendant groups
   - Boundary markers: white pendant cords marking cluster boundaries *)

Inductive CordRole : Type :=
| DataCord
| DividerCord
| BoundaryMarker.

Definition is_divider_color (c : Color) : bool :=
  match c with
  | Red => true
  | White => true
  | Mottled Red White => true
  | Mottled White Red => true
  | _ => false
  end.

Definition is_boundary_color (c : Color) : bool :=
  match c with
  | White => true
  | _ => false
  end.

Record MarkedCord : Type := {
  mc_meta : CordMeta;
  mc_role : CordRole;
  mc_knots : list Knot
}.

Definition infer_role (cm : CordMeta) (ks : list Knot) : CordRole :=
  if is_boundary_color (cm_color cm) && (length ks =? 0) then BoundaryMarker
  else if is_divider_color (cm_color cm) && (length ks =? 0) then DividerCord
  else DataCord.

(* Pendant groups can be delimited by divider cords. *)
Record DelimitedGroup : Type := {
  dg_start_divider : option MarkedCord;
  dg_pendants : list MarkedCord;
  dg_end_divider : option MarkedCord
}.

(* ========================================================================== *)
(*                          MULTI-NUMBER ENCODING                             *)
(* ========================================================================== *)

(* Because figure-eight and long knots only appear in the units position,
   the boundary between consecutive numbers is unambiguous. When a
   figure-eight or long knot is encountered, it marks the units place
   of a number; the next cluster of overhand knots above begins a new
   number's higher places.

   Example: "107, 51" on one cord:
     1 overhand (hundreds=1), gap (tens=0), 7-turn long (units=7),
     5 overhand (tens=5), 1 figure-eight (units=1)
   Read bottom-to-top: first number 107, second number 51. *)

Definition is_units_knot (k : Knot) : bool :=
  match k_kind k with
  | FigureEight => true
  | Long _ => true
  | _ => false
  end.

(* Partition a sorted knot list into segments, each ending with a units knot.
   We use a fuel parameter to ensure termination. *)
Fixpoint partition_by_units_aux (fuel : nat) (acc : list Knot) (ks : list Knot)
  : list (list Knot) :=
  match fuel with
  | 0 => match acc with
         | List.nil => List.nil
         | _ => List.cons (List.rev acc) List.nil
         end
  | S fuel' =>
      match ks with
      | List.nil =>
          match acc with
          | List.nil => List.nil
          | _ => List.cons (List.rev acc) List.nil
          end
      | List.cons k rest =>
          if is_units_knot k then
            List.cons (List.rev (List.cons k acc)) (partition_by_units_aux fuel' List.nil rest)
          else
            partition_by_units_aux fuel' (List.cons k acc) rest
      end
  end.

Definition partition_by_units (ks : list Knot) : list (list Knot) :=
  partition_by_units_aux (length ks) List.nil ks.

(* For multi-number encoding, we need register specs for each number. *)
Definition encode_multi {n : nat} (ns : NumeralSpec n) (nums : list (Vector.t digit n))
  : list Knot :=
  List.concat (List.map (encode ns) nums).

(* ========================================================================== *)
(*                          ACCOUNTING PATTERNS                               *)
(* ========================================================================== *)

(* The Inkawasi khipus (Urton & Chu 2014) revealed arithmetic patterns
   suggesting taxation. Values often satisfy a = b + c where c is a
   fixed "tax" amount (commonly 10 or 15 units). *)

Definition TaxRate : Type := nat.

Definition common_tax_10 : TaxRate := 10.
Definition common_tax_15 : TaxRate := 15.

Record TaxedValue : Type := {
  tv_gross : nat;
  tv_tax : TaxRate;
  tv_net : nat;
  tv_valid : tv_net + tv_tax = tv_gross
}.

Definition compute_tax (gross : nat) (rate : TaxRate) : option TaxedValue.
Proof.
  destruct (rate <=? gross) eqn:Hle.
  - apply Some.
    refine {| tv_gross := gross;
              tv_tax := rate;
              tv_net := gross - rate;
              tv_valid := _ |}.
    apply Nat.leb_le in Hle. lia.
  - exact None.
Defined.

Lemma tax_preserves_value : forall tv,
  tv_net tv + tv_tax tv = tv_gross tv.
Proof.
  intros tv. exact (tv_valid tv).
Qed.

(* A ledger column shows taxation if all entries satisfy the tax pattern. *)
Definition column_shows_tax (values : list nat) (rate : TaxRate) : Prop :=
  forall v, List.In v values -> rate <= v.

Definition column_shows_taxb (values : list nat) (rate : TaxRate) : bool :=
  forallb (fun v => rate <=? v) values.

Lemma column_shows_taxb_spec : forall values rate,
  column_shows_taxb values rate = true <-> column_shows_tax values rate.
Proof.
  intros values rate.
  unfold column_shows_taxb, column_shows_tax.
  rewrite forallb_forall.
  split; intros H v Hin.
  - apply Nat.leb_le. apply H. exact Hin.
  - apply Nat.leb_le. apply H. exact Hin.
Qed.

(* ========================================================================== *)
(*                          PLACE-NAME PREFIXES                               *)
(* ========================================================================== *)

(* Urton & Brezine (2005) discovered that three consecutive figure-eight
   knots at the start of Puruchuco khipus encode the place name—the first
   identified non-numerical "word" in khipu. This suggests khipus could
   have institutional or geographic prefixes. *)

Definition PlacePrefix : Type := list KnotKind.

Definition puruchuco_prefix : PlacePrefix :=
  List.cons FigureEight (List.cons FigureEight (List.cons FigureEight List.nil)).

Definition has_prefix (prefix : PlacePrefix) (ks : list Knot) : bool :=
  let kinds := List.map k_kind ks in
  let prefix_len := length prefix in
  (prefix_len <=? length kinds) &&
  forallb (fun '(a, b) =>
    match a, b with
    | FigureEight, FigureEight => true
    | Overhand, Overhand => true
    | Long t1, Long t2 => tval t1 =? tval t2
    | _, _ => false
    end) (List.combine prefix (List.firstn prefix_len kinds)).

Definition is_puruchuco_khipu (ks : list Knot) : bool :=
  has_prefix puruchuco_prefix ks.

(* ========================================================================== *)
(*                               REFERENCES                                   *)
(* ========================================================================== *)

(*
  === PRIMARY COLONIAL SOURCES (16th-17th century) ===

  Cieza de León, P. Parte Primera de la Crónica del Perú. Seville, 1553.
    First detailed European description of khipu use by Inka administrators.

  Garcilaso de la Vega, I. Comentarios Reales de los Incas. Lisbon, 1609.
    Mestizo chronicler's account of khipu as mnemonic and record-keeping device.

  Guaman Poma de Ayala, F. El Primer Nueva Corónica y Buen Gobierno. 1615.
    Contains iconic illustration of quipucamayoc (khipu keeper) with yupana.
    Manuscript held at Royal Danish Library (GKS 2232 4to).

  === FOUNDATIONAL STUDIES (19th-early 20th century) ===

  Uhle, M. "A Modern Quipu from Cutusuma, Bolivia." Bulletin of the Free
    Museum of the University of Pennsylvania I:51-63, 1897.
    First ethnographic documentation of khipu creation with maker interview.

  Locke, L.L. "The Ancient Quipu, A Peruvian Knot Record." American
    Anthropologist 14(2):325-332, 1912.
    Initial decipherment of decimal positional encoding.

  Locke, L.L. The Ancient Quipu or Peruvian Knot Record. American Museum
    of Natural History, New York, 1923.
    Definitive work establishing knot types and place-value system.

  === MODERN SCHOLARSHIP (late 20th century) ===

  Ascher, M. & Ascher, R. Code of the Quipu: A Study in Media, Mathematics,
    and Culture. University of Michigan Press, Ann Arbor, 1981.
    Republished as Mathematics of the Incas (Dover, 1997).
    Systematic analysis of 200+ khipus; introduced "Ascher relations."

  Conklin, W.J. "The Information System of the Middle Horizon Quipus."
    Annals of the New York Academy of Sciences 385:261-281, 1982.
    Demonstrated Wari khipus predate Inka by 700 years with different conventions.

  === CONTEMPORARY RESEARCH (21st century) ===

  Quilter, J. & Urton, G. (eds.) Narrative Threads: Accounting and Recounting
    in Andean Khipu. University of Texas Press, Austin, 2002.
    Landmark anthology with essays by Ascher, Conklin, Hyland, and others.

  Urton, G. Signs of the Inka Khipu: Binary Coding in the Andean Knotted-
    String Records. University of Texas Press, Austin, 2003.
    Proposed 7-bit binary encoding theory based on construction choices.

  Salomon, F. The Cord Keepers: Khipus and Cultural Life in a Peruvian
    Village. Duke University Press, Durham, 2004.
    Ethnography of Tupicocha village where khipus remained in use until ~1900.

  Urton, G. & Brezine, C. "Khipu Accounting in Ancient Peru." Science
    309(5737):1065-1067, 2005.
    Identified three figure-eight knots as place-name prefix for Puruchuco.

  Brokaw, G. A History of the Khipu. Cambridge University Press, 2010.
    Media studies approach to khipu before and after Spanish conquest.

  Hyland, S. "Ply, Markedness, and Redundancy: New Evidence for How Andean
    Khipus Encoded Information." American Anthropologist 116(3):643-649, 2014.
    Demonstrated S/Z twist correlation with Hanan/Urin moiety organization.

  Urton, G. & Chu, A. "Accounting in the King's Storehouse: The Inkawasi
    Khipu Archive." Latin American Antiquity 26(4):512-529, 2015.
    First khipus found with associated stored goods; revealed tax patterns.

  Hyland, S. "Writing with Twisted Cords: The Inscriptive Capacity of Andean
    Khipus." Current Anthropology 58(3):412-419, 2017.
    Identified 95 distinct signs in Collata epistolary khipus; proposed
    phonetic encoding of lineage names.

  Urton, G. Inka History in Knots: Reading Khipus as Primary Sources.
    University of Texas Press, Austin, 2017.
    Synthesis of 25 years of research on khipu as historical documents.

  Medrano, M. & Urton, G. "Toward the Decipherment of a Set of Mid-Colonial
    Khipus from the Santa Valley, Coastal Peru." Ethnohistory 65(1):1-23, 2018.
    Matched khipu data to 1670 Spanish census; identified recto/verso semantics.

  Clindaniel, J. "Toward a Grammar of the Inka Khipu: Investigating the
    Production of Non-numerical Signs." PhD dissertation, Harvard, 2019.
    Deciphered several non-numerical signs as binary hierarchical pairs.

  Milillo, L. et al. "Heritage Science Contribution to the Understanding of
    Meaningful Khipu Colours." Heritage 6:2355-2378, 2023.
    First scientific analysis of khipu dyes: cochineal, indigo, iron mordants.

  Clindaniel, J. et al. "How Can Data Science Contribute to Understanding
    the Khipu Code?" Latin American Antiquity 35(2):387-407, 2024.
    Computational analysis of 650 khipus; confirmed Ascher relations in 74%;
    identified white cords as boundary markers.

  Medrano, M. et al. "New Insights on Cord Attachment and Social Hierarchy
    in Six Khipus from the Santa Valley, Peru." Ethnohistory 71(4):443-469, 2024.
    First identification of recto/verso attachment as marked/unmarked sign.

  Thompson, K. "A Numerical Connection Between Two Khipus."
    Ethnohistory (online), 2024.
    Connected largest known khipu to complex summary khipu via divider cords.

  Brezine, C. et al. "A New Naming Convention for Andean Khipus."
    Latin American Antiquity 35(3), 2024.
    Standardized nomenclature for khipu scholarship.

  === DATABASES AND DIGITAL RESOURCES ===

  Harvard Khipu Database Project. https://khipukamayuq.fas.harvard.edu
    Founded by Urton and Brezine; contains data on 600+ khipus.

  Open Khipu Repository. https://github.com/khipulab/open-khipu-repository
    Administered by Clindaniel; SQLite database of all published khipu data.

  Khipu Field Guide. https://khipufieldguide.com
    Interactive resource for khipu analysis and visualization.
*)

End Khipu.
