Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
From URM Require Import URM. 

        
    Lemma have_not_halted_means_did_not_halt : forall n, forall p, forall config, fst(execution p config (S n)) = false -> fst(execution p config n) = false.
    Proof.
    -Abort. (* couldn't find the right way to state the theorem *)
    
    Lemma standard_does_not_change_Zn_elements : forall command command':instruction, forall p: program, forall n m q k length_p: nat,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command'
    -> (command = Z n -> command' = Z n).
    Proof. 
        intros command command' p n m q.
        induction p.
        -intros. destruct k;simpl in H;inversion H.
        -intros k length_p. destruct k.
        --intros. simpl in H. inversion H. rewrite H1 in H3. rewrite H3 in H0. simpl in H0. inversion H0. reflexivity.
        --intros. simpl in H. destruct a;simpl in H0;specialize (IHp k length_p); try exact (IHp H H0 H1).
        ---destruct (length_p <? q0);exact (IHp H H0 H1).
    Qed. (* the rest cases are similar*)

    Lemma standard_does_not_change_Ssn_elements : forall command command':instruction, forall p: program, forall n m q k length_p: nat,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command'
    -> (command = Ss n -> command' = Ss n).
    Proof. Admitted.
    
    Lemma standard_does_not_change_Tnm_elements : forall command command':instruction, forall p: program, forall n m q k length_p: nat,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command'
    -> (command = T n m -> command' = T n m).
    Proof. Admitted.
    

    Lemma standard_does_not_change_correct_Jnmq : forall command command': instruction, forall p: program, forall n m q k length_p,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command' -> (length_p <? q) = false
    -> command = J n m q -> command' = J n m q.  
    Proof.
        intros command command' p n m q.
        induction p.
        -intros. destruct k;simpl in H;inversion H.
        -intros. destruct k.
        --intros. simpl in H. inversion H. rewrite H2 in H4. rewrite H4 in H0. simpl in H0.
        rewrite H1 in H0. inversion H0. reflexivity.
        --simpl in H. destruct a;try (simpl in H0;specialize (IHp k length_p);exact (IHp H H0 H1 H2)).
        ---simpl in H0. destruct (length_p <? q0);simpl in H0;try (specialize (IHp k length_p);exact (IHp H H0 H1 H2)).
    Qed.
    (* the next proof is almost the same *)
    Lemma standard_changes_Jnmq_correctly : forall command command': instruction, forall p: program, forall n m q k length_p,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command' -> (length_p <? q) = true
    -> command = J n m q -> command' = J n m (length_p + 1).  
    Proof.
        intros command command' p n m q.
        induction p.
        -intros. destruct k;simpl in H;inversion H.
        -intros. destruct k.
        --intros. simpl in H. inversion H. rewrite H2 in H4. rewrite H4 in H0. simpl in H0.
        rewrite H1 in H0. inversion H0. reflexivity.
        --simpl in H. destruct a;try (simpl in H0;specialize (IHp k length_p);exact (IHp H H0 H1 H2)).
        ---simpl in H0. destruct (length_p <? q0);simpl in H0;try (specialize (IHp k length_p);exact (IHp H H0 H1 H2)).
    Qed.

    Lemma standard_is_correct:  forall command command': instruction, forall p: program, forall n m q k length_p,
    nth_error p k = Some command -> nth_error (standard_form_recursive p length_p) k = Some command'
    ->(command = Z n -> command' = Z n) /\ (command = Ss n -> command' = Ss n)
    /\ (command = T n m -> command' = T n m) /\ ((length_p <? q) = false -> command = J n m q -> command' = J n m q)
    /\ ((length_p <? q) = true -> command = J n m q -> command' = J n m (length_p + 1)).
    Proof. repeat split.
        -eapply standard_does_not_change_Zn_elements; eauto.
        -eapply standard_does_not_change_Ssn_elements; eauto.
        -eapply standard_does_not_change_Tnm_elements; eauto.
        -eapply standard_does_not_change_correct_Jnmq; eauto.
        -eapply standard_changes_Jnmq_correctly; eauto.
    Qed.

    
    Lemma sth_about_join : forall p q,forall config, forall step,
        execution (Join (standard_form p) q) config step = execution q (1, snd(snd(execution p config step))) step.
    Proof. Abort. 
