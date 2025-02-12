Require Import Coq.Init.Logic.
Require Import Coq.Logic.Classical.

Section SpinozaJarrett.
(* UNIVERS *)
Variable U : Type.  (* L'univers des objets *)

(* OPÉRATEURS MODAUX *)
Variable L : Prop -> Prop.  (* Nécessité logique *)
Variable M : Prop -> Prop.  (* Possibilité *)
Variable N : Prop -> Prop.  (* Nécessité naturelle *)

(* LEXIQUE *)
Variable A_1 : U -> Prop. (* x est un attribut *)
Variable B_1 : U -> Prop. (* x est libre *)
Variable D_1 : U -> Prop. (* x est une instance de désir *)
Variable E_1 : U -> Prop. (* x est éternel *)
Variable F_1 : U -> Prop. (* x est fini *)
Variable G_1 : U -> Prop. (* x est un dieu *)
Variable J_1 : U -> Prop. (* x est une instance d'amour *)
Variable K_1 : U -> Prop. (* x est une idée *)
Variable M_1 : U -> Prop. (* x est un mode *)
Variable N_1 : U -> Prop. (* x est nécessaire *)
Variable S_1 : U -> Prop. (* x est une substance *)
Variable T_1 : U -> Prop. (* x est vrai *)
Variable U_1 : U -> Prop. (* x est un intellect *)
Variable W_1 : U -> Prop. (* x est une volonté *)

Variable A_2 : U -> U -> Prop. (* x est un attribut de y *) 
Variable C_2 : U -> U -> Prop. (* x est conçu à travers y *) 
Variable I_2 : U -> U -> Prop. (* x est en y *) 
Variable K_2 : U -> U -> Prop. (* x est cause de y *) 
Variable L_2 : U -> U -> Prop. (* x limite y *) 
Variable M_2 : U -> U -> Prop. (* x est un mode de y *) 
Variable O_2 : U -> U -> Prop. (* x est un objet de y *) 
Variable P_2 : U -> U -> Prop. (* x est la puissance de y *) 
Variable R_2 : U -> U -> Prop. (* x a plus de réalité que y *) 
Variable V_2 : U -> U -> Prop. (* x a plus d'attributs que y *) 

Variable C_3 : U -> U -> U -> Prop.  (* x est commun à y et à z *)
Variable D_3 : U -> U -> U -> Prop.  (* x est divisible entre y et z *)

(* DÉFINITIONS *)

(* D1 : Causa sui - ce dont l'essence implique l'existence *)
Axiom D1 : forall x:U,
  (K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x) <-> L(exists y:U, y = x).

(* D2 : Une chose est finie quand elle peut être limitée par une autre de même nature *)
Axiom D2 : forall x:U,
  F_1 x <-> exists y:U, (y <> x /\ L_2 y x /\ forall z:U, A_2 z x <-> A_2 z y).

(* D3 : Une substance est ce qui est en soi et est conçu par soi *)
Axiom D3 : forall x:U, 
  S_1 x <-> (I_2 x x /\ C_2 x x).

(* D4a : Un attribut est ce que l'intellect perçoit de la substance comme constituant son essence *)
Axiom D4a : forall x:U,
  A_1 x <-> exists y:U, (S_1 y /\ I_2 x y /\ C_2 x y /\ I_2 y x /\ C_2 y x).

(* D4b : x est un attribut de y *)
Axiom D4b : forall x y:U,
  A_2 x y <-> (A_1 x /\ C_2 y x).

(* D5a : Un mode est ce qui est dans autre chose et est conçu par elle *)
Axiom D5a : forall x y:U,
  M_2 x y <-> (x <> y /\ I_2 x y /\ C_2 x y).

(* D5b : x est un mode *)
Axiom D5b : forall x:U,
  M_1 x <-> exists y:U, (S_1 y /\ M_2 x y).

(* D6 : Dieu est une substance constituée d'une infinité d'attributs *)
Axiom D6 : forall x:U,
  G_1 x <-> (S_1 x /\ forall y:U, A_1 y -> A_2 y x).

(* D7a : Une chose est libre quand elle n'est cause que d'elle-même *)
Axiom D7a : forall x:U,
  B_1 x <-> (K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x).

(* D7b : Une chose est nécessaire quand elle est déterminée par autre chose *)
Axiom D7b : forall x:U,
  N_1 x <-> exists y:U, y <> x /\ K_2 y x.

(* D8 : L'éternité est l'existence même en tant que nécessaire *)
Axiom D8 : forall x:U,
  E_1 x <-> L(exists v:U, v = x).

(* AXIOMES *)
(* A1 : Tout ce qui est, est soit en soi, soit en autre chose *)
Axiom A1 : forall x:U,
  I_2 x x \/ exists y:U, y <> x /\ I_2 x y.

(* A2 : Ce qui ne peut être conçu par un autre doit être conçu par soi *)
Axiom A2 : forall x:U,
  (~ exists y:U, y <> x /\ C_2 x y) <-> C_2 x x.

(* A3 : D'une cause déterminée suit nécessairement un effet *)
Axiom A3 : forall x y:U,
  K_2 y x -> N((exists v:U, v = y) <-> exists v:U, v = x).

(* A4 : La connaissance de l'effet dépend de la connaissance de la cause *)
Axiom A4 : forall x y:U,
  K_2 x y <-> C_2 y x.

(* A5 : Les choses qui n'ont rien en commun ne peuvent être conçues l'une par l'autre *)
Axiom A5 : forall x y:U,
  (~ exists z:U, C_3 z x y) <-> (~ C_2 x y /\ ~ C_2 y x).

(* A6 : L'idée vraie doit s'accorder avec son objet *)
Axiom A6 : forall x:U,
  K_1 x -> (T_1 x <-> exists y:U, O_2 y x /\ K_2 x y).

(* A7 : Si une chose peut être conçue comme non existante, son essence n'implique pas l'existence *)
Axiom A7 : forall x:U,
  M(~ exists y:U, y = x) <-> ~ L(exists y:U, y = x).

(* AXIOMES SUPPLÉMENTAIRES *)
(* A8 : Si x est en y alors x est conçu par y *)
Axiom A8 : forall x y:U, I_2 x y -> C_2 x y.

(* A9 : Toute chose a un attribut *)
Axiom A9 : forall x:U, exists y:U, A_2 y x.

(* A10 : Si x est divisible en y et z alors il est possible que x n'existe pas *)
Axiom A10 : forall x y z:U,
  D_3 x y z -> M(~ exists w:U, w = x).
  
(* A11 : Si x est une substance et y limite x alors y est une substance *)
Axiom A11 : forall x y:U,
  S_1 x /\ L_2 y x -> S_1 y.

(* A12 : Si x est un mode de quelque chose alors x est un mode *)
Axiom A12 : forall x:U,
  (exists y:U, M_2 x y) -> M_1 x.

(* A13 : Il est possible qu'un Dieu existe *)
Axiom A13 : M(exists x:U, G_1 x).

(* A14 : x existe nécessairement si et seulement si x n'est pas fini *)
Axiom A14 : forall x:U,
  N(exists y:U, y = x) <-> ~ F_1 x.


(* P1 : Si x est un mode de y et y est une substance, alors x est en y et y est en soi *)
Theorem P1 : forall x y:U, 
  M_2 x y /\ S_1 y -> I_2 x y /\ I_2 y y.
Proof.
  (* On pose nos hypothèses *)
  intros x y [HM HS].

  (* Premièrement, de HS (y est une substance) et D3 (définition de substance), 
     on peut déduire que y est en soi *)
  assert (HIyy: I_2 y y).
  { apply D3 in HS.  (* Par D3 : y substance <-> y en soi et y conçu par soi *)
    destruct HS as [HIyy _]. (* On garde juste y en soi *)
    exact HIyy. 
  }

  (* Deuxièmement, de HM (x est un mode de y) et D5a (définition de mode), 
     on peut déduire que x est en y *)
  assert (HIxy: I_2 x y).
  { apply D5a in HM. (* Par D5a : x mode de y <-> x≠y et x en y et x conçu par y *)
    destruct HM as [_ [HIxy _]]. (* On garde juste x en y *)
    exact HIxy.
  }

  (* Enfin, on combine les deux résultats *)
  split.
  - exact HIxy. (* x est en y *)
  - exact HIyy. (* y est en soi *)
Qed.

Theorem P2 : forall x y:U,
  S_1 x /\ S_1 y /\ x <> y -> ~ exists z:U, C_3 z x y.
Proof.
  (* Introduction des hypothèses *)
  intros x y [HSx [HSy Hxy]].
  
  (* Application de D3 à x *)
  assert (HCx: I_2 x x /\ C_2 x x).
  { apply D3. exact HSx. }
  destruct HCx as [HIxx HCxx].
  
  (* Application de D3 à y *)
  assert (HCy: I_2 y y /\ C_2 y y).
  { apply D3. exact HSy. }
  destruct HCy as [HIyy HCyy].
  
  (* Pour montrer ~C_2 x y *)
  assert (HNoCxy: ~C_2 x y).
  { apply A2 in HCxx.
    intros HC2xy.
    apply HCxx.
    exists y; auto. }
    
  (* Pour montrer ~C_2 y x *)
  assert (HNoCyx: ~C_2 y x).
  { apply A2 in HCyy.
    intros HC2yx.
    apply HCyy.
    exists x; auto. }
    
  (* Conclusion par A5 *)
  apply A5.
  split.
  - exact HNoCxy.
  - exact HNoCyx.
Qed.

(* P3 : Si x et y n'ont rien en commun, alors x ne peut pas être cause de y et y ne peut pas être cause de x *)
Theorem P3 : forall x y:U,
  (~ exists z:U, C_3 z x y) -> ~ K_2 x y /\ ~ K_2 y x.
Proof.
  (* Introduction des hypothèses *)
  intros x y H_no_common.
  
  (* Application de A5 à l'hypothèse : 
     si x,y n'ont rien en commun alors ils ne peuvent être conçus l'un à travers l'autre *)
  apply A5 in H_no_common.
  destruct H_no_common as [H_no_Cxy H_no_Cyx].
  
  (* Nous allons prouver les deux parties de la conjonction *)
  split.
  
  (* Première partie : ~K_2 x y *)
  - intros H_Kxy.
    (* Par A4, si x est cause de y alors y est conçu à travers x *)
    apply A4 in H_Kxy.
    (* Contradiction avec H_no_Cyx *)
    contradiction.
    
  (* Deuxième partie : ~K_2 y x *)
  - intros H_Kyx.
    (* Par A4, si y est cause de x alors x est conçu à travers y *)
    apply A4 in H_Kyx.
    (* Contradiction avec H_no_Cxy *)
    contradiction.
Qed.

(** x neq y -> y neq x *)
Lemma neq_sym : forall x y:U, 
  x <> y -> y <> x.
Proof.
  intros x y H.
  intro Heq.
  apply H.
  symmetry.
  exact Heq.
Qed.

(* x est une substance ssi x est en soi *)
Lemma DP1 : forall x:U,
  S_1 x <-> I_2 x x.
Proof.
  intros. split.
  - intro. apply D3 in H. destruct H. exact H.
  - intro. apply D3. split.
    + assumption.
    + apply A8. assumption.
Qed.


(** DP5 : Toute chose est soit une substance soit un mode *)
Lemma DP5 : forall x:U,
  S_1 x \/ M_1 x.
Proof.
  intro. pose proof (A1 x). destruct H.
  - left. apply DP1. assumption.
  - right. destruct H as [y [H1 H2]].
    pose proof (A8 _ _ H2). apply A12.
    exists y. apply D5a. split.
    + apply neq_sym. assumption.
    + split; assumption.
Qed.


(** DP6 : Une substance et un mode ne peuvent jamais être la même chose *)
Lemma DP6 : forall x:U,
  ~(S_1 x /\ M_1 x).
Proof.
  intros x [HS HM].
  (* x est un mode donc il existe une substance y dont x est le mode (D5b) *)
  apply D5b in HM. destruct HM as [y [HSy HMxy]].
  (* x est un mode de y donc conçu par y (D5a) *)
  apply D5a in HMxy. destruct HMxy as [Hneq [_ HCxy]].
  (* x est une substance donc conçu par soi (D3) *)
  apply D3 in HS. destruct HS as [_ HCxx].
  (* Par A2, si x est conçu par soi, il ne peut être conçu par autre chose *)
  apply A2 in HCxx.
  apply HCxx.
  exists y.
  split.
  - apply neq_sym in Hneq. exact Hneq.
  - exact HCxy.
Qed.

(* DP7 : Si x est un attribut de y et y est une substance, alors x = y *)
Lemma DP7 : forall x y:U, A_2 x y /\ S_1 y -> x = y.
Proof.
  (* Introduction des hypothèses *)
  intros x y [HA2 HS].
  
  (* De HA2 (x est un attribut de y) et D4b, on obtient que y est conçu à travers x *)
  apply D4b in HA2.
  destruct HA2 as [_ HCyx].
  
  (* De HS (y est une substance) et D3, on obtient que y est conçu par soi *)
  apply D3 in HS.
  destruct HS as [_ HCyy].
  
  (* Par A2, si y est conçu par soi, il ne peut être conçu par autre chose *)
  apply A2 in HCyy.
  
  (* Preuve par l'absurde : supposons x ≠ y *)
  assert (H: x = y).
  { (* Par le tiers exclu, soit x = y soit x ≠ y *)
    apply NNPP. (* Not Not P -> P *)
    intro Hneq.
    (* Si x ≠ y, alors y serait conçu à travers quelque chose d'autre que soi *)
    apply HCyy.
    exists x.
    split.
    - exact Hneq.
    - exact HCyx.
  }
  exact H.
Qed.



Theorem P4 : forall x y:U,
  x <> y -> exists z z':U, 
    (((A_2 z x /\ A_2 z' x /\ z <> z') \/ 
     (A_2 z x /\ z = x /\ M_1 y)) \/ 
     (A_2 z' y /\ z' = y /\ M_1 x)) \/ 
     (M_1 x /\ M_1 y).
Proof.
Admitted.

End SpinozaJarrett.
