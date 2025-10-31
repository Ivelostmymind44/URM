Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.


    Definition reg := nat -> nat.
    Definition reg0 : nat -> nat := (fun _ => 0).
    Lemma reg0_is_correct: forall x : nat, reg0 x = 0.
    Proof. reflexivity. Qed.

    Definition update_value (f : nat -> nat)(x : nat) (v : nat) :=
    (fun x' => if Nat.eqb x x' then v else f x').

    Example fl: forall f: nat -> nat, (update_value f 6 5) 6 = 5.
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

    Lemma standard_recursive_does_not_change_length : forall p:program, forall length_p: nat,
         length(p) = length(standard_form_recursive p length_p).
    Proof. intros. induction p.
        -reflexivity.
        -destruct a;try rewrite IHp;simpl; try (rewrite IHp; reflexivity).
        destruct (length_p <? q);simpl; try (rewrite IHp;reflexivity).
    Qed.  

    Lemma standard_does_not_change_length : forall p: program, length p = length (standard_form p).
    Proof. intros. apply standard_recursive_does_not_change_length.
    Qed.


    (* Join or concatenation of two programs *)
    Fixpoint Concat_recursive (Q : program) (length_p : nat) : program :=
    match Q with 
    | [] => []
    | J n m q :: Q' => J n m (q + (length_p)) :: Concat_recursive Q' length_p
    | h :: Q' => h :: Concat_recursive Q' length_p
    end.
    Definition Join (p q: program) : program := p ++ Concat_recursive q (length p).
        (* acts well whenever p is in its standard form*)


    (* Substitution *)
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

    
    (* move_and_compute G n m l := G[n,...,m -> l] as defined in the book
       (with this difference that registers in the left side are chosen sequentially here)*)
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


    (* Recursion *)
    Definition m_recusion f g n := max (n+2) (max (ru f) (ru g)).
    
    Definition neat_recursion f g n m t q p := 
    (transfer_x_to_m (n+1) m 1) ++ [T (t+1) (t+3);Z (t+1)] ++ (move_and_compute f 1 (n+1) (t+2))
    ++ [J (t+1) (t+3) p] ++ (move_and_compute g (m+1) (m+n+2) (t+2)) ++ [Ss (t+1)] ++ [J 1 1 q;T (t+2) 1].
    
    Definition recursion f g n := neat_recursion f g n (m_recusion f g n) ((m_recusion f g n)+n) (n+1+2+(length (move_and_compute f 1 (n+1) ((m_recusion f g n)+n+2)))+1) (n+1+2+(length (move_and_compute f 1 (n+1) (((m_recusion f g n)+n)+2)))+1+(length (move_and_compute g ((m_recusion f g n)+1) ((m_recusion f g n)+n+2) (((m_recusion f g n)+n)+2)))+3).

    (* Minimalisation *)
    Definition neat_minimalisation f n m p q := 
        (transfer_x_to_m (n) m 1) ++ (move_and_compute f (m+1) (m+n+1) 1) ++ [J 1 (m+n+2) q;Ss (m+n+1);J 1 1 p;T (m+n+1) 1].
        
    Definition minimalisation f n := neat_minimalisation f n (max (n+1) (ru f)) (n+1) (n+(length (move_and_compute f ((max (n+1) (ru f))+1) ((max (n+1) (ru f))+n+1) 1))+4).
