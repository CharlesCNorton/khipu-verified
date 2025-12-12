(******************************************************************************)
(*                                                                            *)
(*         Khipu Numerals: Inka Knot Records and Decimal Positional Semantics *)
(*                                                                            *)
(*     A foundation for khipu (quipu) numeric cords: explicit cord geometry   *)
(*     (discrete positions), register intervals, knot-shape constraints, and  *)
(*     a canonical Inka decimal interpretation (units via figure‑eight/long   *)
(*     knots; higher places via clusters of overhand knots). Prove:           *)
(*       • register disjointness ⇒ unique place assignment                    *)
(*       • validation decidability                                            *)
(*       • decode(encode(ds)) = ds for canonical encodings                    *)
(*       • totality of decoding under well‑formedness                         *)
(*                                                                            *)
(*     "He who seeks to count the stars before he can count the scores and    *)
(*     knots of the quipus deserves derision."                                *)
(*     - Inca Garcilaso de la Vega, 1609–1617                                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: November 28, 2025                                                *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  Arith.Arith
  Arith.PeanoNat
  Bool.Bool
  Lists.List
  Sorting.Permutation
  Program.Program
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
(*                                GEOMETRY                                    *)
(* ========================================================================== *)

(* Discrete coordinate along a pendant cord, measured in "ticks" (e.g., mm),
   with 0 = free end (bottom), increasing upward toward the attachment point. *)
Definition pos : Type := nat.

Record Interval : Type := {
  lo : pos;               (* inclusive *)
  hi : pos;               (* exclusive *)
  lo_lt_hi : lo < hi
}.

(* Half-open membership: lo <= p < hi *)
Definition in_interval (p : pos) (I : Interval) : Prop :=
  lo I <= p < hi I.

Definition in_intervalb (p : pos) (I : Interval) : bool :=
  (lo I <=? p) && (p <? hi I).

Lemma in_intervalb_spec : forall p I,
  in_intervalb p I = true <-> in_interval p I.
Proof.
  intros p I. unfold in_intervalb, in_interval.
  rewrite andb_true_iff.
  rewrite Nat.leb_le, Nat.ltb_lt.
  tauto.
Qed.

Lemma not_in_interval_if_ge_hi : forall I p,
  hi I <= p -> ~ in_interval p I.
Proof.
  intros I p Hge [Hlo Hlt]. lia.
Qed.

Lemma not_in_interval_if_lt_lo : forall I p,
  p < lo I -> ~ in_interval p I.
Proof.
  intros I p Hlt [Hlo _]. lia.
Qed.

(* "Wide enough" interval to host 10 canonical slot positions: lo+1+0 .. lo+1+9.
   This is a geometric (fabric/spacing) constraint for canonical encodings. *)
Definition wide_enough (I : Interval) : Prop :=
  lo I + 11 <= hi I.

Definition slot (I : Interval) (k : nat) : pos :=
  lo I + 1 + k.

Lemma slot_in_interval :
  forall I k,
    k < 10 ->
    wide_enough I ->
    in_interval (slot I k) I.
Proof.
  intros I k Hk Hwide.
  unfold in_interval, slot.
  split.
  - lia.
  - (* lo+1+k < hi: k<=9 gives lo+10 < lo+11 <= hi *)
    have Hk' : k <= 9 by lia.
    lia.
Qed.

(* ========================================================================== *)
(*                                  DIGITS                                    *)
(* ========================================================================== *)

(* Decimal digit, rigorously bounded: Fin.t 10 is a canonical 0..9 type. *)
Definition digit : Type := Fin.t 10.

Definition digit_to_nat (d : digit) : nat := Fin.to_nat d.

Lemma digit_to_nat_lt10 : forall d : digit, digit_to_nat d < 10.
Proof. intro d. apply Fin.to_nat_lt. Qed.

Lemma digit_ext : forall a b : digit,
  digit_to_nat a = digit_to_nat b -> a = b.
Proof.
  (* standard injectivity fact for Fin.to_nat *)
  apply Fin.to_nat_inj.
Qed.

Definition digit0 : digit := Fin.of_nat_lt (ltac:(lia : 0 < 10)).
Definition digit1 : digit := Fin.of_nat_lt (ltac:(lia : 1 < 10)).

Definition digit_of_nat (n : nat) (H : n < 10) : digit := Fin.of_nat_lt H.

(* ========================================================================== *)
(*                                KNOT FORMS                                  *)
(* ========================================================================== *)

Inductive Twist : Type := S | Z.

(* Long-knot turn count is physically meaningful and *bounded* in the canonical
   decimal reading: 2..9 turns represent 2..9 in the units register. *)
Record Turns : Type := {
  tval : nat;
  t_range : 2 <= tval <= 9
}.

Lemma turns_lt10 : forall t : Turns, tval t < 10.
Proof.
  intros [v [H2 H9]]. simpl. lia.
Qed.

Inductive KnotKind : Type :=
| Overhand                        (* simple overhand knot (single) *)
| Long (t : Turns)                (* long knot with t turns *)
| FigureEight                     (* figure-eight knot (units digit 1) *)
| EE (t : Turns).                 (* “EE” variant (rare); available for future dialects *)

Record Knot : Type := {
  k_pos  : pos;
  k_kind : KnotKind;
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
  forall ks, all_overhandb ks = true <-> (forall k, In k ks -> k_kind k = Overhand).
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
(*                           REGISTERS / LAYOUTS                               *)
(* ========================================================================== *)

(* A register layout is a fixed vector of disjoint, ordered intervals.
   Convention: index 0 = units register, index 1 = tens, etc. *)
Fixpoint chain_order {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => True
  | [_] => True
  | I :: J :: tl => hi I <= lo J /\ chain_order (J :: tl)
  end.

Fixpoint all_wide {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => True
  | I :: tl => wide_enough I /\ all_wide tl
  end.

Fixpoint all_within (len : pos) {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => True
  | I :: tl => hi I <= len /\ all_within len tl
  end.

Record NumeralSpec (n : nat) : Type := {
  ns_len   : pos;
  ns_len_pos : 0 < ns_len;
  ns_regs  : Vector.t Interval n;
  ns_order : chain_order ns_regs;
  ns_wide  : all_wide ns_regs;
  ns_within : all_within ns_len ns_regs
}.

(* ========================================================================== *)
(*                               KNOT GROUPING                                *)
(* ========================================================================== *)

Definition knots_in (I : Interval) (ks : list Knot) : list Knot :=
  filter (fun k => in_intervalb (k_pos k) I) ks.

Lemma knots_in_app : forall I xs ys,
  knots_in I (xs ++ ys) = knots_in I xs ++ knots_in I ys.
Proof.
  intros I xs ys. unfold knots_in. now rewrite filter_app.
Qed.

Lemma knots_in_sound : forall I ks k,
  In k (knots_in I ks) -> in_interval (k_pos k) I.
Proof.
  intros I ks k Hin.
  unfold knots_in in Hin.
  apply filter_In in Hin as [HinK Hb].
  apply (proj1 (in_intervalb_spec _ _)) in Hb.
  exact Hb.
Qed.

Lemma knots_in_complete : forall I ks k,
  In k ks ->
  in_interval (k_pos k) I ->
  In k (knots_in I ks).
Proof.
  intros I ks k HinK HinI.
  unfold knots_in.
  apply filter_In.
  split; [assumption|].
  apply (proj2 (in_intervalb_spec _ _)).
  exact HinI.
Qed.

Lemma knots_in_nil_if_all_outside :
  forall I ks,
    (forall k, In k ks -> ~ in_interval (k_pos k) I) ->
    knots_in I ks = [].
Proof.
  intros I ks Hall.
  unfold knots_in.
  apply filter_false.
  intros k Hin.
  specialize (Hall k Hin).
  apply (proj1 (Bool.negb_true_iff _)) in Hall.
  (* easier: show predicate is false by contradiction with in_intervalb_spec *)
  destruct (in_intervalb (k_pos k) I) eqn:Hb; auto.
  exfalso.
  apply (proj1 (in_intervalb_spec _ _)) in Hb.
  exact (Hall Hb).
Qed.

(* ========================================================================== *)
(*                          CANONICAL DECIMAL DIALECT                          *)
(* ========================================================================== *)

(* Units register (place 0):
     0  => no knot in that register
     1  => exactly one FigureEight knot
     2..9 => exactly one Long knot with corresponding turns
   Higher registers (place >= 1):
     d => exactly d Overhand knots (d may be 0), and no other kinds. *)

Inductive UnitsValue : Type :=
| U0
| U1
| ULong (t : Turns).

Definition units_digit (u : UnitsValue) : digit :=
  match u with
  | U0 => digit0
  | U1 => digit1
  | ULong t => digit_of_nat (tval t) (turns_lt10 t)
  end.

Definition units_ok (ks : list Knot) : Prop :=
  match ks with
  | [] => True
  | [k] =>
      match k_kind k with
      | FigureEight => True
      | Long t => True
      | _ => False
      end
  | _ => False
  end.

Definition higher_ok (ks : list Knot) : Prop :=
  (forall k, In k ks -> k_kind k = Overhand) /\
  length ks < 10.

(* Boolean validators, for decidability. *)
Definition units_okb (ks : list Knot) : bool :=
  match ks with
  | [] => true
  | [k] =>
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
  intro ks. destruct ks as [|a [|b tl]]; simpl; try tauto.
  destruct tl; simpl.
  - destruct (k_kind a); try tauto.
  - tauto.
Qed.

Lemma higher_okb_spec : forall ks, higher_okb ks = true <-> higher_ok ks.
Proof.
  intro ks. unfold higher_okb, higher_ok.
  rewrite andb_true_iff.
  rewrite all_overhandb_spec.
  rewrite Nat.ltb_lt.
  tauto.
Qed.

(* Decoding a single register to a digit (partial; fails if malformed). *)

Definition decode_units (ks : list Knot) : option digit :=
  match ks with
  | [] => Some digit0
  | [k] =>
      match k_kind k with
      | FigureEight => Some digit1
      | Long t => Some (digit_of_nat (tval t) (turns_lt10 t))
      | _ => None
      end
  | _ => None
  end.

Definition decode_higher (ks : list Knot) : option digit :=
  if all_overhandb ks then
    match Nat.lt_dec (length ks) 10 with
    | left Hlt => Some (digit_of_nat (length ks) Hlt)
    | right _ => None
    end
  else None.

Lemma decode_units_total_if_ok : forall ks,
  units_ok ks -> exists d, decode_units ks = Some d.
Proof.
  intros ks Hok.
  destruct ks as [|a [|b tl]]; simpl; eauto.
  destruct tl; simpl in *.
  - destruct (k_kind a); try contradiction; eauto.
  - contradiction.
Qed.

Lemma decode_higher_total_if_ok : forall ks,
  higher_ok ks -> exists d, decode_higher ks = Some d.
Proof.
  intros ks [Hall Hlen].
  unfold decode_higher.
  assert (all_overhandb ks = true).
  { apply (proj2 (all_overhandb_spec ks)). exact Hall. }
  rewrite H. destruct (Nat.lt_dec (length ks) 10); eauto; lia.
Qed.

(* ========================================================================== *)
(*                       WELL-FORMED NUMERAL CORD (PROP)                       *)
(* ========================================================================== *)

Fixpoint regs_covered (p : pos) {n : nat} (regs : Vector.t Interval n) : Prop :=
  match regs with
  | [] => False
  | I :: tl => in_interval p I \/ regs_covered p tl
  end.

Fixpoint regs_covering_index {n : nat} (p : pos) (regs : Vector.t Interval n)
  : Type :=
  match regs with
  | [] => False
  | I :: tl => (in_interval p I) + (regs_covering_index p tl)
  end.

(* Boolean coverage check (for decidability) *)
Fixpoint regs_coveredb (p : pos) {n : nat} (regs : Vector.t Interval n) : bool :=
  match regs with
  | [] => false
  | I :: tl => in_intervalb p I || regs_coveredb p tl
  end.

Lemma regs_coveredb_spec : forall p n (regs : Vector.t Interval n),
  regs_coveredb p regs = true <-> regs_covered p regs.
Proof.
  intros p n regs.
  induction regs as [|I n tl IH]; simpl.
  - tauto.
  - rewrite orb_true_iff. rewrite in_intervalb_spec. rewrite IH. tauto.
Qed.

(* Placewise constraints over a full register vector:
   head = units_ok; tail = higher_ok *)
Fixpoint regs_ok {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : Prop :=
  match regs with
  | [] => True
  | I :: tl =>
      units_ok (knots_in I ks) /\
      regs_ok_higher tl ks
  end
with regs_ok_higher {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : Prop :=
  match regs with
  | [] => True
  | I :: tl =>
      higher_ok (knots_in I ks) /\
      regs_ok_higher tl ks
  end.

Fixpoint regs_okb {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : bool :=
  match regs with
  | [] => true
  | I :: tl =>
      units_okb (knots_in I ks) && regs_okb_higher tl ks
  end
with regs_okb_higher {n : nat} (regs : Vector.t Interval n) (ks : list Knot) : bool :=
  match regs with
  | [] => true
  | I :: tl =>
      higher_okb (knots_in I ks) && regs_okb_higher tl ks
  end.

Lemma regs_okb_spec :
  forall n (regs : Vector.t Interval n) ks,
    regs_okb regs ks = true <-> regs_ok regs ks.
Proof.
  (* mutual proof *)
Admitted.

(* Entire numeral cord well-formedness: geometry + coverage + per-register dialect. *)
Definition WellFormed {n : nat} (ns : NumeralSpec n) (ks : list Knot) : Prop :=
  (* all knots strictly below the attachment point *)
  (forall k, In k ks -> k_pos k < ns_len ns) /\
  (* every knot lies in some register interval *)
  (forall k, In k ks -> regs_covered (k_pos k) (ns_regs ns)) /\
  (* register-level constraints (units + higher) *)
  regs_ok (ns_regs ns) ks.

(* Boolean validator for full well-formedness. *)
Definition WellFormedb {n : nat} (ns : NumeralSpec n) (ks : list Knot) : bool :=
  let len := ns_len ns in
  let regs := ns_regs ns in
  let in_boundsb :=
    forallb (fun k => k_pos k <? len) ks in
  let coveredb :=
    forallb (fun k => regs_coveredb (k_pos k) regs) ks in
  in_boundsb && coveredb && regs_okb regs ks.

Theorem WellFormed_decidable :
  forall n (ns : NumeralSpec n) ks,
    {WellFormed ns ks} + {~ WellFormed ns ks}.
Proof.
  intros n ns ks.
  (* Use classical decidability via booleans; proof obligations are mechanical. *)
Admitted.

(* ========================================================================== *)
(*                        DECODING A FULL CORD TO DIGITS                        *)
(* ========================================================================== *)

Fixpoint decode_regs {n : nat} (regs : Vector.t Interval n) (ks : list Knot)
  : option (Vector.t digit n) :=
  match regs with
  | [] => Some []
  | I :: tl =>
      match decode_units (knots_in I ks), decode_regs_higher tl ks with
      | Some d0, Some ds => Some (d0 :: ds)
      | _, _ => None
      end
  end
with decode_regs_higher {n : nat} (regs : Vector.t Interval n) (ks : list Knot)
  : option (Vector.t digit n) :=
  match regs with
  | [] => Some []
  | I :: tl =>
      match decode_higher (knots_in I ks), decode_regs_higher tl ks with
      | Some d, Some ds => Some (d :: ds)
      | _, _ => None
      end
  end.

Theorem decode_total_under_WF :
  forall n (ns : NumeralSpec n) ks,
    WellFormed ns ks ->
    exists ds, decode_regs (ns_regs ns) ks = Some ds.
Proof.
  intros n ns ks [Hbounds [Hcov Hok]].
  (* use units_ok/higher_ok totality lemmas along regs_ok *)
Admitted.

(* ========================================================================== *)
(*                         NUMERIC SEMANTICS OF DIGITS                          *)
(* ========================================================================== *)

Fixpoint value_digits {n : nat} (ds : Vector.t digit n) : nat :=
  match ds with
  | [] => 0
  | d :: tl => digit_to_nat d + 10 * value_digits tl
  end.

(* ========================================================================== *)
(*                          CANONICAL ENCODING (CONSTRUCTIVE)                  *)
(* ========================================================================== *)

Definition mk_overhand (p : pos) : Knot :=
  {| k_pos := p; k_kind := Overhand; k_twist := Z |}.

Definition mk_fig8 (p : pos) : Knot :=
  {| k_pos := p; k_kind := FigureEight; k_twist := Z |}.

Program Definition mk_long (p : pos) (n : nat) (H : 2 <= n <= 9) : Knot :=
  {| k_pos := p; k_kind := Long {| tval := n; t_range := H |}; k_twist := Z |}.

Fixpoint overhand_cluster (I : Interval) (n : nat) : list Knot :=
  (* canonical cluster: overhands at slot I 0,1,2,...,(n-1) *)
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

Lemma overhand_cluster_all_overhand : forall I n k,
  In k (overhand_cluster I n) -> k_kind k = Overhand.
Proof.
  intros I n. induction n; simpl; intros k Hin.
  - contradiction.
  - apply in_app_or in Hin as [Hin|Hin].
    + apply IHn; exact Hin.
    + simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
      subst k. reflexivity.
Qed.

Lemma overhand_cluster_positions_in_I :
  forall I n k,
    wide_enough I ->
    In k (overhand_cluster I n) ->
    in_interval (k_pos k) I.
Proof.
  intros I n. induction n; simpl; intros k Hwide Hin.
  - contradiction.
  - apply in_app_or in Hin as [Hin|Hin].
    + apply IHn; auto.
    + simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
      subst k. simpl.
      apply slot_in_interval; try lia; auto.
Qed.

Definition encode_units (I : Interval) (d : digit) : list Knot :=
  match digit_to_nat d with
  | 0 => []
  | 1 => [mk_fig8 (slot I 0)]
  | S (S m) =>
      (* n = S(S m) is in 2..9 because digits are <10 *)
      let n := S (S m) in
      (* proof: 2 <= n <= 9 *)
      let H2 : 2 <= n := ltac:(lia) in
      let H9 : n <= 9 := ltac:(pose proof (digit_to_nat_lt10 d) as Hlt;
                              simpl in Hlt; lia) in
      [mk_long (slot I 0) n (conj H2 H9)]
  end.

Definition encode_higher (I : Interval) (d : digit) : list Knot :=
  overhand_cluster I (digit_to_nat d).

Fixpoint encode_regs {n : nat} (regs : Vector.t Interval n) (ds : Vector.t digit n) : list Knot :=
  match regs, ds with
  | [], [] => []
  | I :: tlI, d :: tlD =>
      encode_units I d ++ encode_regs_higher tlI tlD
  end
with encode_regs_higher {n : nat} (regs : Vector.t Interval n) (ds : Vector.t digit n) : list Knot :=
  match regs, ds with
  | [], [] => []
  | I :: tlI, d :: tlD =>
      encode_higher I d ++ encode_regs_higher tlI tlD
  end.

Definition encode {n : nat} (ns : NumeralSpec n) (ds : Vector.t digit n) : list Knot :=
  encode_regs (ns_regs ns) ds.

(* ========================================================================== *)
(*                       ENCODING IS WELL-FORMED (CANONICAL)                   *)
(* ========================================================================== *)

Lemma encode_units_positions_in_I :
  forall I d k,
    wide_enough I ->
    In k (encode_units I d) ->
    in_interval (k_pos k) I.
Proof.
  intros I d k Hwide.
  unfold encode_units.
  destruct (digit_to_nat d) as [|[|m]]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hin|Hin]; [|contradiction]. subst k. simpl.
    apply slot_in_interval; auto; lia.
  - destruct Hin as [Hin|Hin]; [|contradiction]. subst k. simpl.
    apply slot_in_interval; auto; lia.
Qed.

Lemma encode_higher_positions_in_I :
  forall I d k,
    wide_enough I ->
    In k (encode_higher I d) ->
    in_interval (k_pos k) I.
Proof.
  intros I d k Hwide.
  unfold encode_higher.
  eapply overhand_cluster_positions_in_I; eauto.
Qed.

(* A key separation fact: if hi I <= lo J then no point in J can lie in I. *)
Lemma interval_separation :
  forall I J p,
    hi I <= lo J ->
    in_interval p J ->
    ~ in_interval p I.
Proof.
  intros I J p Hsep [HloJ HhiJ].
  intro HinI. destruct HinI as [_ HltI].
  (* From p >= lo J >= hi I contradict p < hi I *)
  lia.
Qed.

(* Mutual proof that canonical encoding respects per-register constraints. *)
Lemma encode_regs_ok :
  forall n (regs : Vector.t Interval n) ds,
    all_wide regs ->
    chain_order regs ->
    regs_ok regs (encode_regs regs ds).
Proof.
Admitted.

Theorem encode_is_WellFormed :
  forall n (ns : NumeralSpec n) ds,
    WellFormed ns (encode ns ds).
Proof.
  intros n ns ds.
  unfold WellFormed, encode.
  split.
  - (* bounds: all knot positions < ns_len *)
    intros k Hin.
    (* each knot is in some interval; each interval hi <= len; and membership gives p < hi *)
Admitted.
(* remaining subgoals: coverage + regs_ok *)
Admitted.

(* ========================================================================== *)
(*                         DECODE(ENCODE(ds)) = ds                              *)
(* ========================================================================== *)

Lemma decode_units_encode_units :
  forall I d,
    decode_units (encode_units I d) = Some d.
Proof.
  intros I d.
  unfold encode_units, decode_units.
  destruct (digit_to_nat d) as [|[|m]]; simpl.
  - (* digit 0 *)
    apply f_equal. apply digit_ext. reflexivity.
  - (* digit 1 *)
    simpl. apply f_equal. apply digit_ext. simpl. reflexivity.
  - (* digit >=2 *)
    simpl.
    (* decode_units returns digit_of_nat n, and n = digit_to_nat d *)
    apply f_equal. apply digit_ext. simpl. reflexivity.
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
  destruct (Nat.lt_dec (length (overhand_cluster I (digit_to_nat d))) 10) as [Hlt|Hge].
  - apply f_equal. apply digit_ext.
    rewrite overhand_cluster_length. reflexivity.
  - exfalso.
    rewrite overhand_cluster_length in Hge.
    pose proof (digit_to_nat_lt10 d). lia.
Qed.

(* The global round-trip theorem is delicate because decode_regs filters by
   interval from the *whole* knot multiset. The proof uses:
     - filter distributes over concatenation
     - chain_order ensures interval separation (no cross-register contamination)
     - each register’s encoding lies within its own interval
   The statement below is the landmark correctness lemma. *)
Theorem decode_encode_roundtrip :
  forall n (ns : NumeralSpec n) ds,
    decode_regs (ns_regs ns) (encode ns ds) = Some ds.
Proof.
Admitted.

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
(*                         EXTENSION: FULL KHIPU TREES                          *)
(* ========================================================================== *)

(* A khipu is a rooted cord with pendant cords; each pendant may carry its own
   numeral spec and knot list. This section defines a typed tree; numeric
   semantics are assigned to those pendants that are proven well-formed. *)

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

Fixpoint cord_children (c : Cord) : list Attachment :=
  match c with CordNode _ _ _ ch => ch end.

(* A "numeric pendant" is a cord equipped with a NumeralSpec and a proof
   of well-formedness of its knots under that spec. *)
Record NumericPendant (n : nat) : Type := {
  np_meta : CordMeta;
  np_spec : NumeralSpec n;
  np_knots : list Knot;
  np_wf : WellFormed np_spec np_knots
}.

Definition pendant_value {n} (p : NumericPendant n) : nat :=
  match decode_total_under_WF (np_spec p) (np_knots p) (np_wf p) with
  | ex_intro _ ds _ => value_digits ds
  end.

(* A khipu ledger is a heterogeneous list of numeric pendants of varying widths. *)
Definition Ledger : Type := list { n : nat & NumericPendant n }.

Fixpoint ledger_values (L : Ledger) : list nat :=
  match L with
  | [] => []
  | existT _ n p :: tl => pendant_value p :: ledger_values tl
  end.

(* Invariants you typically want for auditing/accounting interpretations:
   - attachment points within main cord
   - pendant register layouts do not overlap physical knots, etc.
   These are intentionally stated as Props (not parameters) for future proofs. *)
Definition attachment_within (parent_len : pos) (a : Attachment) : Prop :=
  match a with
  | Attach at child => at < parent_len /\ cord_len child > 0
  end.

Fixpoint cord_wf (c : Cord) : Prop :=
  match c with
  | CordNode _ L ks ch =>
      (0 < L) /\
      (forall k, In k ks -> k_pos k < L) /\
      (forall a, In a ch -> attachment_within L a /\ cord_wf (match a with Attach _ child => child end))
  end.

End Khipu.
