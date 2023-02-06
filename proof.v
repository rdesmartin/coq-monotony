Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zorder.
From Coq Require Import Lia.

Require Import Coq.Classes.RelationClasses.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint dot_product (l1: list Z) (l2: list Z) : Z
  := match (l1, l2) with
    | (nil, _)          => 0
    | (_, nil)          => 0
    | (h1::t1, h2::t2) => h1 * h2 + (dot_product t1 t2)
    end.

Inductive list_all: (Z -> Prop) -> list Z -> Prop
:=  | la_nil pred : list_all pred nil
    | la_cons (pred: Z -> Prop) (hd: Z) tl : pred hd -> list_all pred tl -> list_all pred (hd :: tl).

Example list_all1 :
  list_all (fun x => (0 <= x)%Z) [1; 2; 3]%Z.
Proof.
  repeat (constructor; try apply Pos2Z.is_nonneg).
  Qed.
  
Example list_all2:
  list_all (fun x => (x <= 0)%Z) [-2; 0]%Z.
Proof.
  repeat (constructor; try lia).
Qed.
  
Example list_all3:
  ~ list_all (fun x => (x <= 0)%Z) [-2; 1]%Z.
  Proof.
    intros H.
    inversion H; subst.
    inversion H4; subst.
    lia. 
    Qed.

Inductive all_positive: list Z -> Prop
:=  | ap_nil : all_positive nil
    | ap_cons (hd: Z) tl : (0 <= hd)%Z -> all_positive tl -> all_positive (hd :: tl).

Example allpos1 :
  all_positive [ 1%Z; 2%Z; 3%Z ].
Proof.
  repeat (constructor; try apply Pos2Z.is_nonneg).
  Qed.

Example allpos2 :
  ~ all_positive [ 1%Z; 2%Z; (-3)%Z ].
Proof.
  intros H. inversion H; subst. 
  inversion H3; subst.
  inversion H5; subst.
  lia. Qed.

Inductive ge_list : list Z -> list Z -> Prop
:= | ge_nil: ge_list nil nil
   | ge_l1_l2 h1 t1 h2 t2: (h1 >= h2)%Z -> ge_list t1 t2 -> ge_list (h1::t1) (h2::t2).

Example ge_list_1: ge_list [1; 2; 3]%Z [1; 2; 3]%Z.
Proof.
  repeat (constructor; try lia). Qed.

Example ge_list_2: ge_list [1; 2; 3]%Z nil -> False.
Proof.
  intros. inversion H. Qed.

Example ge_list_3: ge_list [1; 3]%Z [1; 2]%Z.
Proof.
  repeat (constructor; try lia). Qed.


Inductive monotonous: (Z -> Z) -> Prop
:= | cons f : forall m n, ((n <= m)%Z -> (f n <= f m)%Z) -> monotonous f.


Lemma hd_pos: forall (n: Z) (l: list Z),
  all_positive (n::l) -> (0 <= n)%Z.
Proof.
  intros n l H.
  inversion H; subst. assumption. Qed.

Lemma tl_pos : forall (n : Z) (l: list Z),
  all_positive (n::l) -> all_positive l.
Proof.
  intros n l H.
  inversion H; subst. assumption. Qed.


Theorem pos_dot_product: forall (l1 l2: list Z),
  all_positive l1 -> all_positive l2 -> (0 <= (dot_product l1 l2))%Z.
Proof.
  induction l1 as [| h1 t1 IH1].
  (* l1 = nil *)
  - reflexivity.
  (* l1 = h1::t1 *)
  - destruct l2 as [|h2 t2].
    (* l2 = nil *)
    * reflexivity.
    (* l2 = h2::t2 *)
    * intros pos1 pos2.
      inversion pos1; subst.
      inversion pos2; subst.
      simpl.
      assert (pos_tl_prod: (0 <= dot_product t1 t2)%Z).
      { apply IH1. assumption. assumption. }
      lia. Qed.

Definition Perceptron_t : Type := (Z -> Z) -> (list Z) -> Z -> (list Z) -> Z.

Definition perceptron (act: Z -> Z) (w: list Z) (b: Z) (input: list Z)
  := act (b + dot_product w input)%Z.
  
Definition perceptron' w b i := (b + dot_product w i)%Z.

Definition thresh k x := if (x <=? k)%Z then x else k.

Lemma flip_ge: forall m n,
  (m >= n)%Z -> (n <= m)%Z.
Proof.
  lia. Qed.

Lemma dp_pos_monotony: forall (w m n: list Z),
  all_positive w ->
  all_positive n ->
  all_positive m -> 
  ge_list m n ->
  (dot_product w n <= dot_product w m)%Z.
Proof.
  induction w as [| hw tw IHw].
  - reflexivity.
  - intros m n pos_w pos_n pos_m ge_mn.
    inversion pos_w; subst.
    destruct n as [| hn tn].
    * destruct m.
      ** reflexivity.
      ** simpl. inversion pos_m; subst.
         assert (pos_tw_m: (0 <= dot_product tw m)%Z).
         { 
          apply pos_dot_product.
          assumption.
          assumption.
         }
         lia.
    * destruct m as [| hm tm].
      ** inversion ge_mn.
      ** simpl.
         assert (dot_product tw tn <= dot_product tw tm)%Z.
         { 
          apply IHw.
          assumption.
          inversion pos_n; subst; assumption.
          inversion pos_m; subst; assumption.
          inversion ge_mn; subst; assumption.
         }
         assert (hw * hn <= hw * hm)%Z.
         {
          inversion pos_m; subst.
          inversion pos_n; subst.
          inversion ge_mn; subst.
          apply flip_ge in H9. (* flip hm >= hn to hn <= hm *)
          (* the lia tactic did not work automatically here *)
          apply Z.mul_le_mono_nonneg_l.
          assumption. assumption.
          }
          lia.
    Qed.

Theorem perceptron_monotony: forall (b: Z) (w m n: list Z) f,
  all_positive w ->
  all_positive m ->
  all_positive n ->
  (0 <= b)%Z ->
  monotonous f ->
  ge_list m n ->
  (perceptron f w b n <= perceptron f w b m)%Z.
Proof.
  intros b w m n f pos_w pos_m pos_n pos_b mon_f ge_mn.
  change (f (b + dot_product w n) <= f (b + dot_product w m))%Z.
  assert (le_dp: (dot_product w n <= dot_product w m)%Z).
  { apply dp_pos_monotony. assumption. assumption. assumption. assumption. }
  assert (le_z: (b + dot_product w n <= b + dot_product w m)%Z ).
  { lia. }
  inversion mon_f.
  Abort.