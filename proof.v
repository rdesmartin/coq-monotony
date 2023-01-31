Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zorder.

Require Import Coq.Classes.RelationClasses.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint dot_product (l1: list Z) (l2: list Z) : Z
  := match (l1, l2) with
    | (nil, _)          => 0
    | (_, nil)          => 0
    | (h1::t1, h2::t2) => (Z.mul h1 h2) + (dot_product t1 t2)
    end.

Inductive AllPositive: list Z -> Prop
:=  | AllPosNil : AllPositive nil
    | AllPosCons (hd: Z) tl : (0 <= hd)%Z -> AllPositive tl -> AllPositive (hd :: tl).

Example allpos1 :
  AllPositive [ 1%Z; 2%Z; 3%Z ].
Proof. 
  apply AllPosCons. apply Pos2Z.is_nonneg.
  apply AllPosCons. apply Pos2Z.is_nonneg.
  apply AllPosCons. apply Pos2Z.is_nonneg.
  apply AllPosNil. Qed.


Goal forall (n : Z) l, (~ nil = n :: l).
  Proof.
    intros n z H.
    (* This tactic replaces the goal with an equivalent one. *)
  change (match (@nil Z) with
          | nil => False
          | n :: z => True
          end
    ).
    (* simpl. *)
    rewrite H.
    constructor.
    Qed.

Goal 0 <> 1.
Proof.
  intros H.
  change (match O with 
          | O   => False
          | S _ => True
          end
  ).
  rewrite H. constructor.
  Qed.

Example allpos2 :
  ~ AllPositive [ 1%Z; 2%Z; (-3)%Z ].
Proof.
  intros H. inversion H. subst. 
  inversion H3. subst.
  inversion H5. subst.
  Admitted.

Lemma hd_pos: forall (n: Z) (l: list Z),
  AllPositive (n::l) -> (0 <= n)%Z.
Proof.
  intros n l H.
  inversion H. subst. apply H2. Qed.

Lemma tl_pos : forall (n : Z) (l: list Z),
  AllPositive (n::l) -> AllPositive l.
Proof.
  intros n l H.
  inversion H. subst. apply H3. Qed.

Lemma lte_flip_gte : forall (n m: Z),
  (n <= m)%Z -> (m >= n)%Z.
  intros n m H.
  apply Zorder.Zle_not_lt in H.
  apply Znot_lt_ge in H. 
  apply H. Qed.

Theorem pos_dot_product: forall (l1 l2: list Z),
  AllPositive l1 -> AllPositive l2 -> (0 <= (dot_product l1 l2))%Z.
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
      



(* Initial unsuccessful attempt using a fixpoint function *)

Notation "x && y" := (andb x y).

Fixpoint all_positive (l: list Z) : bool
:= match l with
  | nil => true
  | hd :: tl => (0 <=? hd)%Z && (all_positive tl)
  end.


Lemma hd_pos' : forall (n: Z) (l: list Z),
  all_positive (n::l) = true -> (0 <= n)%Z.
Proof.
  intros n l H.
  destruct n.
  (* n = 0 *)
  - reflexivity.
  (* n = Z.pos p *)
  - rewrite <- Pos2Z.is_nonneg. reflexivity.
  (* n = Z.neg p : reductio ad absurdum, induction hypothesis cannot be true.*)
  - discriminate. Qed.

Lemma tl_pos' : forall (n: Z) (l: list Z),
  all_positive (n::l) = true -> all_positive l = true.
Proof. 
  intros n l H.
  induction l as [| n' l' IH].
  - reflexivity.
  - simpl. assert (H2: (0 <=? n)%Z = true).
    * Abort.


Theorem pos_dot_product': forall (l1 l2: list Z),
     (all_positive l1 = true) 
  -> (all_positive l2) = true 
  -> (0 <= dot_product l1 l2)%Z.
Proof.
  intros l1.
  induction l1 as [| n1 l1' IH1].
  - reflexivity.
  - induction l2 as [| n2 l2' IH2].
    * reflexivity.
    * simpl.
    Abort.

  
  
  
  
  