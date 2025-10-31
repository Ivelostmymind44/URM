Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
From URM Require Import URM. 

    Definition Example2_1:= [J 1 2 6;Ss 2;Ss 3;J 1 2 6;J 1 1 2;T 3 1].    
    Lemma exe1 : output Example2_1 (update_value (update_value reg0 1 9) 2 7) 12 = 2.
     Proof. reflexivity. Qed.
    Lemma exer2_2 : output Example2_1 (update_value (update_value (update_value reg0 1 8) 2 4) 3 2) 17 = 6.
     Proof. reflexivity. Qed.
    
    Lemma never_stops_extension : forall n, forall in_reg, forall m, m<3 -> fst(execution [Ss 1;J 1 1 1] (m,in_reg) (n)) = false.
     Proof. induction n.
        -reflexivity.
        -intros. simpl.
        assert (self_eqb :forall n : nat, (n =? n) = true). {intros n0. apply Nat.eqb_eq. reflexivity. }
        destruct m.
        -- simpl. apply IHn. lia.
        -- destruct m.
        --- simpl. apply IHn. lia.
        --- destruct m.
        ----simpl. rewrite self_eqb. apply IHn. lia.
        ----lia.
    Qed. 

    Lemma never_stops : forall n, forall in_reg, fst(execution [Ss 1;J 1 1 1] (1,in_reg) (n)) = false.
    Proof. intros. apply never_stops_extension. lia. Qed.
        
    Lemma exer2_3_extension :  forall n, forall in_reg, forall m, (in_reg 1 <? in_reg 2) = true -> m < 6 -> fst(snd(execution Example2_1 (m,in_reg) (n))) < 6.
     Proof. induction n.
        - simpl. lia.
        -destruct m.
        --intros. (*destruct H.*) simpl. destruct (in_reg 1 =? in_reg 2) eqn:ths.
        +admit. 
        +apply IHn. apply H. lia.
        -- destruct m.
        --- simpl. intros. destruct (in_reg 1 =? in_reg 2) eqn:ths.
        +admit.
        +apply IHn. apply H. lia.
        ---destruct m.
        ----simpl. intros. specialize (IHn (update_value in_reg 2 (S (in_reg 2)))). apply IHn. unfold update_value. simpl.
         admit. lia.
        ----destruct m.
        -----simpl. intros. specialize (IHn (update_value in_reg 3 (S (in_reg 3)))). apply IHn. unfold update_value. simpl.
         apply H. lia.
        -----destruct m.
        +simpl. intros.  destruct (in_reg 1 =? in_reg 2) eqn:ths.
        ++admit.
        ++apply IHn. apply H. lia.
        +destruct m.
        +++intros. simpl. assert (self_eqb :forall n : nat, (n =? n) = true). {intros n0. apply Nat.eqb_eq. reflexivity. }
        rewrite self_eqb. apply IHn. apply H. lia.
        +++destruct m; intros; lia.
    Admitted. (* Qed. *)

    Lemma exer2_3: forall n, fst(snd(execution Example2_1 (1, (update_value (update_value reg0 1 2) 2 3)) (n))) < 6.
     Proof. intros. eapply exer2_3_extension. unfold update_value. reflexivity. lia. Qed.
    

    Definition ADD := [J 3 2 5;Ss 1;Ss 3;J 1 1 1].
    Definition MINUS_ONE := [J 1 4 9;Ss 2;J 1 2 7; Ss 3;Ss 2;J 1 1 3;T 3 1].
    Definition HALF_FOR_EVEN := [J 1 3 6;Ss 2;Ss 3;Ss 3;J 1 1 1;T 2 1].

    Definition exer3_3_1a:= [J 1 2 4;Z 1;Ss 1].
    Definition exer3_3_1b:= [Z 1;Ss 1;Ss 1;Ss 1;Ss 1;Ss 1].
    Definition exer3_3_1c:= [J 1 2 5;Z 1;Ss 1;J 1 1 6;Z 1].
    (* there's more exercises here *)

    
(* Substitution part *)
    (* rearrengement *)
    Fixpoint re_list lst :=
    match lst with 
    |[] => []
    |n :: t => Projection_function n :: re_list t
    end.
    Definition perrutation f per := Combine f (re_list per) (length per).

    
    (* Example 3.3*)
    Fixpoint combine_repeat m (f: program) P n : program :=
    match m with
    |O => Combine f P n
    |S m' => combine_repeat m' (Combine f P n) P n
    end.
    Definition constant x:= if x =? 0 then [Z 1] else (combine_repeat (x-1) Identity_function [[Ss 1]] 1).
    Compute constant 1.
    Compute output (constant 0) reg0 1000.
    Example constant_function : forall m n x: nat, forall config:state, snd(snd (execution (Join [Z 1] (combine_repeat m Identity_function [[Ss 1]] 1)) config n)) 1= m.
    Proof. -Abort.

(* recursion part *)
    Definition cut_off_by_one := recursion Zero_function (Projection_function 2) 1.
    Compute cut_off_by_one.
    Compute output cut_off_by_one (update_value reg0 2 10) 100.
        (* Theorem 4.5 and others *)
        (* bounded universal and existential quantifier can be sirulated by recursion*)

    (* minimalisation part *)
        (* exercise 5.4 *)



