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
    | (h1::t1, h2::t2) => (Z.mul h1 h2) + (dot_product t1 t2)
    end.

Inductive all_positive: list Z -> Prop
:=  | ap_nil : all_positive nil
    | ap_cons (hd: Z) tl : (0 <= hd)%Z -> all_positive tl -> all_positive (hd :: tl).

Example allpos1 :
  all_positive [ 1%Z; 2%Z; 3%Z ].
Proof. 
  apply ap_cons. apply Pos2Z.is_nonneg.
  apply ap_cons. apply Pos2Z.is_nonneg.
  apply ap_cons. apply Pos2Z.is_nonneg.
  apply ap_nil. Qed.

Example allpos2 :
  ~ all_positive [ 1%Z; 2%Z; (-3)%Z ].
Proof.
  intros H. inversion H. subst. 
  inversion H3. subst.
  inversion H5. subst.
  lia. Qed.
  
(*    | ge_nil_l l2: ge_list nil l2
   | ge_nil_r l1: ge_list l1 nil   *)

Inductive ge_list : list Z -> list Z -> Prop
:= | ge_nil: ge_list nil nil
   | ge_l1_l2 h1 t1 h2 t2: (h1 >= h2)%Z -> ge_list t1 t2 -> ge_list (h1::t1) (h2::t2).

Example ge_list_1: ge_list [1; 2; 3]%Z [1; 2; 3]%Z.
Proof.
  apply ge_l1_l2. lia.
  apply ge_l1_l2. lia.
  apply ge_l1_l2. lia.
  apply ge_nil. Qed.
  
Example ge_list_2: ge_list [1; 2; 3]%Z nil -> False.
Proof.
  intros. inversion H. Qed.

Example ge_list_3: ge_list [1; 3]%Z [1; 2]%Z.
Proof.
  apply ge_l1_l2. lia.
  apply ge_l1_l2. lia.
  apply ge_nil. Qed.

Lemma hd_pos: forall (n: Z) (l: list Z),
  all_positive (n::l) -> (0 <= n)%Z.
Proof.
  intros n l H.
  inversion H. subst. apply H2. Qed.

Lemma tl_pos : forall (n : Z) (l: list Z),
  all_positive (n::l) -> all_positive l.
Proof.
  intros n l H.
  inversion H. subst. apply H3. Qed.


Theorem pos_dot_product: forall (l1 l2: list Z),
  all_positive l1 -> all_positive l2 -> (0 <= (dot_product l1 l2))%Z.
Proof.
  induction l1 as [| h1 t1 IH1].
  (* l1 = nil *)
  - reflexivity.
  (* l1 = h1::t1 *)
  - induction l2 as [|h2 t2 IH2].
    (* l2 = nil *)
    * reflexivity.
    (* l2 = h2::t2 *)
    * intros pos1 pos2.
      apply hd_pos in pos1 as hdpos1.
      apply hd_pos in pos2 as hdpos2.
      apply tl_pos in pos1 as tlpos1.
      apply tl_pos in pos2 as tlpos2.
      simpl.
      assert (pos_tl_prod: (0 <= dot_product t1 t2)%Z).
      { apply IH1. apply tlpos1. apply tlpos2. }
      assert (pos_hd_prod: (0 <= h1 * h2)%Z).
      { change ((0 * h2 <= h1 * h2)%Z). 
        apply Zmult_le_compat_r. 
        apply hdpos1. apply hdpos2.
      }
      apply Z.add_nonneg_nonneg.
      apply pos_hd_prod. apply pos_tl_prod.
      Qed.

Definition Perceptron_t : Type := (Z -> Z) -> (list Z) -> Z -> (list Z) -> Z.

Definition perceptron (act: Z -> Z) (w: list Z) (b: Z) (input: list Z)
  := act (b + dot_product input w)%Z.
  
Definition perceptron' w b i := (b + dot_product w i)%Z.

Lemma flip_ge: forall m n,
  (m >= n)%Z -> (n <= m)%Z.
Proof.
  lia. Qed.

Lemma dp_lte: forall (w m n: list Z),
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
         assert (H7: (dot_product tw tn <= dot_product tw tm)%Z).
         { 
          apply IHw.
          assumption.
          inversion pos_n; subst; assumption.
          inversion pos_m; subst; assumption.
          inversion ge_mn; subst; assumption.
         }
         assert (H8: (hw * hn <= hw * hm)%Z).
         {
          inversion pos_w; subst.
          inversion pos_m; subst.
          inversion pos_n; subst.
          inversion ge_mn; subst.
          apply flip_ge in H11.
          admit.
          }
    Abort.


Theorem perceptron_monotony: forall (b: Z) (w m n: list Z),
  all_positive w ->
  all_positive n ->
  (0 <= b)%Z ->
  ge_list m n ->
  (perceptron' w b n <= perceptron' w b m)%Z.
Proof.
  Abort.
  
  
  