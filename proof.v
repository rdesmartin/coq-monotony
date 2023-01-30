Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.ZArith.BinInt.

Require Import Coq.Classes.RelationClasses.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint dot_product (l1: list Z) (l2: list Z) : Z
  := match (l1, l2) with
    | (nil, _)          => 0
    | (_, nil)          => 0
    | (h1::t1, h2::t2) => (Z.mul h1 h2) + (dot_product t1 t2)
    end.

Notation "x && y" := (andb x y).

Fixpoint all_positive (l: list Z) : bool
:= match l with
  | nil => true
  | hd :: tl => (0 <=? hd)%Z && (all_positive tl)
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

Example allpos2 :
  AllPositive [ 1%Z; 2%Z; (-3)%Z ] -> False.
Proof.
  Admitted.

(* Using the fixpoint function *)
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

(* Using the induction type *)
Lemma hd_pos: forall (n: Z) (l: list Z),
  AllPositive (n::l) -> (0 <= n)%Z.
Proof.
  intros n l H.
  Admitted.

(* Using the fixpoint function *)
Lemma tl_pos : forall (n: Z) (l: list Z),
  all_positive (n::l) = true -> all_positive l = true.
Proof. 
  intros n l H.
  induction l as [| n' l' IH].
  - reflexivity.
  - simpl. assert (H2: (0 <=? n)%Z = true).
    * Admitted.

Theorem pos_dot_product': forall (l1 l2: list Z),
  (all_positive l1 = true) -> (all_positive l2) = true -> (0 <= dot_product l1 l2)%Z.
Proof.
  intros l1 l2 H1 H2.
  induction l1 as [| n1 l1' IH1].
  - reflexivity.
  - induction l2 as [| n2 l2' IH2].
    * reflexivity.
    * simpl. rewrite IH2.
    Admitted.

Theorem pos_dot_product: forall (l1 l2: list Z),
  (AllPositive l1) -> (AllPositive l2) -> (0 <= dot_product l1 l2)%Z.
Proof.
  intros l1 l2 Posl1 Posl2.
  Admitted.
  
  
  
  
  
  
  
  