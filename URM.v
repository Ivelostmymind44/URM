Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
(* From LF Require Export Maps. *)
Require Import List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.


Module URM.
    Definition reg := nat -> nat.
    Definition reg0 : nat -> nat :=
    (fun _ => 0).
    Lemma reg0_is_correct: forall x : nat, reg0 x = 0.
    Proof. reflexivity. Qed.
    Definition update_value
                (f : nat -> nat)(x : nat) (v : nat) :=
    (fun x' => if Nat.eqb x x' then v else f x').
    Example fl: forall f: nat -> nat, update_value f 6 5 6 = 5.
    Proof. reflexivity. Qed.


    Lemma update_value_is_correct : forall x x' n, forall f, (update_value f x n) x = n /\ ((x=?x') = false -> ((update_value f x n) x' = f x')).
    Proof. split.
        unfold update_value. rewrite Nat.eqb_refl. reflexivity.
        intros. unfold update_value. destruct (x =? x') eqn:ths.
        -inversion H.
        -reflexivity.
    Qed.

    Definition state := prod nat (nat -> nat).
    Inductive instruction : Type := 
     |Z (n : nat)
     |Ss (n: nat) 
     |T (n m : nat)
     |J (n m q : nat).

     Definition program := list instruction. 

     Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
    Notation "[ ]" := nil.
    Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
    Notation "x ++ y" := (app x y)
            (right associativity, at level 60).

    Definition Example2_1:= [J 1 2 6;Ss 2;Ss 3;J 1 2 6;J 1 1 2;T 3 1].
    Example ss : length [Z (0);Ss(1);T 2 3] = 3.
     Proof. reflexivity. Qed.
    Example sd : [Z (0)] ++ [Ss(1) ; T 2 3] = [Z (0);Ss(1);T 2 3].
     Proof. reflexivity. Qed.
    

    Definition Zero_function := [Z 1].
    Definition Successor_function := [S 1].
    Definition Projection_function i := [T i 1].
    Definition Identity_function := [T 1 1]. (*Just a simple dummy program that does not change the value of first register *)
    Compute Projection_function 5.

    Definition one_step_execution (command : instruction)
    (config : state) : state :=
    match command with (* add option to determine the end of a execution*)
     |(Z (n)) => ((fst config) + 1, update_value (snd config) n 0)
     |(Ss (n)) => ( (fst config) + 1, update_value (snd config) n (1 + (snd config n)))
     |(T n m) => ((fst config) + 1, update_value (snd config) m (snd config n))
     |(J n m q) => if Nat.eqb (snd config n) (snd config m)
         then (q, snd config) else (1 + (fst config), snd config)
    end.
    
    Lemma one_step_is_correct_on_Zn : forall  config : state, forall n : nat,
    one_step_execution (Z (n)) (config) = ((fst config) + 1, update_value (snd config) n 0).
     Proof. reflexivity. Qed.
    (* others are just as immediate as this one *)

        

   Fixpoint execution (p : program) (config : (prod nat (nat -> nat)))  (step : nat) 
   :prod bool (prod nat (nat -> nat)) :=
   match step with 
   |O => (false, config)
   |S n => match nth_error p ((fst config)-1) with (* cause list is 0 base but registers aren't *)
            |None => (true, (((fst config) -1) , snd config)) (* line can be changed to length_p+1*)
            |Some command => execution p (one_step_execution command config) n 
            end
    end. (* Here in this definition, true means it has halted in "step" steps or less *)

    Definition output p in_reg step := (snd(snd(execution p (1, in_reg) step)) 1).
    
    Definition initial_config := (1, reg0). 
    (* note that every computation for a program with another initial config,
      can be sirulated with a program with (1, reg0) config*)


    Compute (execution [] initial_config 5).    
    Compute (execution [Ss 1 ; T 1 2] (1, reg0) 5).
    Compute (execution [Ss 1 ; T 1 2; J 1 1 1] (1, reg0) 5).    

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
        --simpl. apply IHn. lia.
        -- destruct m.
        --- 
        (* inversion ths.  *)
        simpl. apply IHn. lia.
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
        (* lia. rewrite H. rewrite H1. simpl. apply IHn. lia. lia. *)
        -- destruct m.
        --- simpl. intros. destruct (in_reg 1 =? in_reg 2) eqn:ths.
        +admit.
        +apply IHn. apply H. lia.
         (* rewrite H. rewrite H1. apply IHn. lia. lia. *)
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

    Lemma have_not_halted_means_did_not_halt : forall n, forall p, forall config, fst(execution p config (S n)) = false -> fst(execution p config n) = false.
    Proof.
    -Abort. (* couldn't find the right way to state the theorem *)
    
    
    Definition ADD := [J 3 2 5;Ss 1;Ss 3;J 1 1 1].
    Definition MINUS_ONE := [J 1 4 9;Ss 2;J 1 2 7; Ss 3;Ss 2;J 1 1 3;T 3 1].
    Definition HALF_FOR_EVEN := [J 1 3 6;Ss 2;Ss 3;Ss 3;J 1 1 1;T 2 1].

    Definition exer3_3_1a:= [J 1 2 4;Z 1;Ss 1].
    Definition exer3_3_1b:= [Z 1;Ss 1;Ss 1;Ss 1;Ss 1;Ss 1].
    Definition exer3_3_1c:= [J 1 2 5;Z 1;Ss 1;J 1 1 6;Z 1].
    (* there's more exercises here *)

    Fixpoint standard_form_recursive (p: program) (length_p: nat) : program :=
    match p with
    |[] => []
    |J n m q :: p1 => if Nat.ltb (length_p) q 
    then J n m ((length_p) + 1) :: (standard_form_recursive p1 length_p) 
    else J n m q :: (standard_form_recursive p1 length_p)
    |command :: p1 => command :: standard_form_recursive p1 length_p
    end.
    Definition standard_form (p: program) := standard_form_recursive p (length p).

    Compute standard_form [J 1 1 5].
    Compute standard_form [J 1 1 1].
    Compute standard_form [J 1 1 2].
    Compute standard_form [J 1 1 3;J 1 1 3].

    Lemma standard_recursive_does_not_change_length : forall p:program, forall length_p: nat, length(p) = length(standard_form_recursive p length_p).
    Proof. intros. induction p.
        -reflexivity.
        -destruct a;try rewrite IHp;simpl; try (rewrite IHp; reflexivity).
        destruct (length_p <? q);simpl; try (rewrite IHp;reflexivity).
    Qed.  

    Lemma standard_does_not_change_length : forall p: program, length p = length (standard_form p).
    Proof. intros. apply standard_recursive_does_not_change_length.
    Qed.


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



    Fixpoint Concat_recursive (Q : program) (length_p : nat) : program :=
    match Q with 
    | [] => []
    | J n m q :: Q' => J n m (q + (length_p)) :: Concat_recursive Q' length_p
    | h :: Q' => h :: Concat_recursive Q' length_p
    end.

    Definition Join (p q: program) : program := p ++ Concat_recursive q (length p).
        (* acts well whenever p is in its standard form*)

    Lemma sth_about_join : forall p q,forall config, forall step,
        execution (Join (standard_form p) q) config step = execution q (1, snd(snd(execution p config step))) step.
    Proof. Abort. 
    
    Fixpoint ru_recursive (p : program) ( k : nat) : nat :=
    match p with 
    |[] => k
    |Z n :: t =>  ru_recursive t (max n k)
    |Ss n :: t =>  ru_recursive t (max n k)
    |T n m :: t =>  ru_recursive t (max n (max m k))
    |J n m q :: t => ru_recursive t (max n (max m k))
    end.

    Definition ru p : nat := ru_recursive p 0.
    Compute ru [Ss 97; J 64 54 103].


    Fixpoint move_to (p : program) (l : nat) : program :=
    match p with 
    |[] => []
    |Z n :: t =>  Z (n + l) :: move_to t l
    |Ss n :: t =>  Ss (n+l) :: move_to t l
    |T n m :: t =>  T (n+l) (m+l) :: move_to t l
    |J n m q :: t => J (n+l) (m+l) q :: move_to t l
    end.
    Compute move_to [Ss 97; J 64 54 103].
    Compute move_to [Ss 97; J 64 54 103] 5.
    
    Fixpoint move_it_from_thisToThat_to_first (n m counter: nat): program :=
    match m with
    |O => []
    |S m' => T (n + counter - 1) (counter) :: move_it_from_thisToThat_to_first n m' (S counter)
    end.
    Compute move_it_from_thisToThat_to_first 5 (12-5+1) 1.

    Fixpoint Clear_from_thisToThat (n m counter: nat): program := 
    match m with
    |O => []
    |S m' => Z (n + counter - 1) :: Clear_from_thisToThat n m' (S counter)
    end.
    Compute Clear_from_thisToThat 5 (12-5+1) 1.


    (* move_and_compute := move_it_from_thisToThat_to_first_then_compute_and_put_output_there*)
    Definition move_and_compute (p: program) (n m l: nat): program :=
    (move_it_from_thisToThat_to_first n (m-n+1) 1) ++ (Clear_from_thisToThat (n+1) (ru p - (n+1)) 1 ) ++ p ++ [T 1 l].
    Compute move_and_compute [Ss 5; T 6 4] 5 7 11.


    Fixpoint m_combine ( max_f : nat ) (P : list program): nat := 
    match P with 
    |[]=> max_f
    |p :: t => m_combine (max (ru p) max_f) t 
    end.    

    Fixpoint combine_programs_of_P (P : list program) ( n m counter : nat) : program :=
    match P with
    |[] => []
    |p :: t => move_and_compute p (m+1) (m+n) (n+m+counter) ++ combine_programs_of_P t n m (S counter)
    end.


    Fixpoint transfer_x_to_m (n m counter :nat):program:=
    match n with 
    |O => []
    |S n' => T counter (m + counter) :: transfer_x_to_m n' m (S counter) 
    end.
    Compute transfer_x_to_m 5 6 1.

    Definition neat_Combine (f : program) (P : list program) ( n m k : nat): program :=
        (transfer_x_to_m n m 1) ++ (combine_programs_of_P P n m 1) ++ (move_and_compute f (m + n + 1) (m+n+k) 1).

    Definition Combine (f : program) (P : list program) ( n : nat): program := (* every p in P has n inputs *)
        neat_Combine f P n (m_combine (max n (max (length P) (ru f))) P) (length P).

    Compute Combine Identity_function [[Ss 1]] 1.

    
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

    Definition m_recusion f g n := max (n+2) (max (ru f) (ru g)).
    Definition neat_recursion f g n m t q p := (transfer_x_to_m (n+1) m 1) ++ [T (t+1) (t+3);Z (t+1)] ++ (move_and_compute f 1 (n+1) (t+2)) ++ [J (t+1) (t+3) p] ++ (move_and_compute g (m+1) (m+n+2) (t+2)) ++ [Ss (t+1)] ++ [J 1 1 q;T (t+2) 1] .
    Definition recursion f g n := neat_recursion f g n (m_recusion f g n) ((m_recusion f g n)+n) (n+1+2+(length (move_and_compute f 1 (n+1) ((m_recusion f g n)+n+2)))+1) (n+1+2+(length (move_and_compute f 1 (n+1) (((m_recusion f g n)+n)+2)))+1+(length (move_and_compute g ((m_recusion f g n)+1) ((m_recusion f g n)+n+2) (((m_recusion f g n)+n)+2)))+3).
    
    Definition cut_off_by_one := recursion Zero_function (Projection_function 2) 1.
    Compute cut_off_by_one.
    Compute output cut_off_by_one (update_value reg0 2 10) 100.
    (* Theorem 4.5 and others *)
    (* bounded universal and existential quantifier can be sirulated by recursion*) 

    Definition neat_minimalization f n m p q := (transfer_x_to_m (n) m 1) ++ (move_and_compute f (m+1) (m+n+1) 1) ++ [J 1 (m+n+2) q;Ss (m+n+1);J 1 1 p;T (m+n+1) 1].
    Definition minimalization f n := neat_minimalization f n (max (n+1) (ru f)) (n+1) (n+(length (move_and_compute f ((max (n+1) (ru f))+1) ((max (n+1) (ru f))+n+1) 1))+4).
    (* exercise 5.4 *)


End URM.
