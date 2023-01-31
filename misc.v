(* Explanation of discriminate tactic's under the hood *)

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