(******************************************************************************)
(*                                                                            *)
(*         Khipu Numerals: Inka Knot Records and Decimal Positional Semantics *)
(*                                                                            *)
(*     Formalizes khipu numeric cords with register-based decimal encoding.   *)
(*     Proves unique place assignment, validation decidability, and           *)
(*     decode/encode roundtrip correctness.                                   *)
(*                                                                            *)
(*     "He who seeks to count the stars before he can count the scores and    *)
(*      knots of the quipus deserves derision." - Inca Garcilaso de la Vega   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 12, 2025                                                *)
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

(* Discrete coordinate along a pendant cord, measured in ticks.
   0 = free end (bottom), increasing upward toward the attachment point. *)
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

Inductive Twist : Type := TS | TZ.

(* Long-knot turn count (canonical units reading): 2..9 turns represent 2..9. *)
Record Turns : Type := {
  tval : nat;
  t_range : 2 <= tval <= 9
}.

Lemma turns_lt10 : forall t : Turns, tval t < 10.
Proof.
  intros [v [H2 H9]]. simpl. lia.
Qed.

Inductive KnotKind : Type :=
| Overhand
| Long (t : Turns)
| FigureEight
| EE (t : Turns).

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

(* Units (place 0):
     0  => no knot
     1  => exactly one FigureEight
     2..9 => exactly one Long with corresponding turns
   Higher places (>=1):
     d => exactly d Overhand knots (d may be 0) and no other kinds. *)

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
(*                         EXTENSION: FULL KHIPU TREES                          *)
(* ========================================================================== *)

Parameter Color : Type.
Parameter Fiber : Type.

Record CordMeta : Type := {
  fiber : Fiber;
  color : Color;
  spin  : Twist;  (* spin direction *)
  ply   : Twist   (* ply direction *)
}.

Inductive Cord : Type :=
| CordNode : CordMeta -> pos -> list Knot -> list Attachment -> Cord
with Attachment : Type :=
| Attach : pos -> Cord -> Attachment.

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
  | Attach p child => p < parent_len /\ cord_len child > 0
  end.

Inductive cord_wf : Cord -> Prop :=
| cord_wf_node : forall m L ks ch,
    0 < L ->
    (forall k, List.In k ks -> k_pos k < L) ->
    attachments_wf L ch ->
    cord_wf (CordNode m L ks ch)
with attachments_wf : pos -> list Attachment -> Prop :=
| attachments_wf_nil : forall L, attachments_wf L List.nil
| attachments_wf_cons : forall L p child tl,
    p < L ->
    cord_len child > 0 ->
    cord_wf child ->
    attachments_wf L tl ->
    attachments_wf L (List.cons (Attach p child) tl).

End Khipu.
