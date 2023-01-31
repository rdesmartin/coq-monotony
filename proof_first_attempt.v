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

  
  
  
  
  
