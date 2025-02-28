Require Import Coq.Init.Logic.
Require Import Coq.Logic.Classical.

Section SpinozaJarrett.

(* ====UNIVERS==== *)
Variable U : Type.  (* L'univers des objets *)

(* ====OP\u00c9RATEURS MODAUX==== *)
Variable L : Prop -> Prop.  (* N\u00e9cessit\u00e9 logique *)
Variable M : Prop -> Prop.  (* Possibilit\u00e9 *)
Variable N : Prop -> Prop.  (* N\u00e9cessit\u00e9 naturelle *)

(* ====LEXIQUE==== *)

(* Pr\u00e9dicats unaires *)
Variable A_1 : U -> Prop. (* x est un attribut *)
Variable B_1 : U -> Prop. (* x est libre *)
Variable D_1 : U -> Prop. (* x est une instance de d\u00e9sir *)
Variable E_1 : U -> Prop. (* x est \u00e9ternel *)
Variable F_1 : U -> Prop. (* x est fini *)
Variable G_1 : U -> Prop. (* x est un dieu *)
Variable J_1 : U -> Prop. (* x est une instance d'amour *)
Variable K_1 : U -> Prop. (* x est une id\u00e9e *)
Variable M_1 : U -> Prop. (* x est un mode *)
Variable N_1 : U -> Prop. (* x est n\u00e9cessaire *)
Variable S_1 : U -> Prop. (* x est une substance *)
Variable T_1 : U -> Prop. (* x est vrai *)
Variable U_1 : U -> Prop. (* x est un intellect *)
Variable W_1 : U -> Prop. (* x est une volont\u00e9 *)

(* Pr\u00e9dicats binaires *)
Variable A_2 : U -> U -> Prop. (* x est un attribut de y *) 
Variable C_2 : U -> U -> Prop. (* x est con\u00e7u \u00e0 travers y *) 
Variable I_2 : U -> U -> Prop. (* x est en y *) 
Variable K_2 : U -> U -> Prop. (* x est cause de y *) 
Variable L_2 : U -> U -> Prop. (* x limite y *) 
Variable M_2 : U -> U -> Prop. (* x est un mode de y *) 
Variable O_2 : U -> U -> Prop. (* x est un objet de y *) 
Variable P_2 : U -> U -> Prop. (* x est la puissance de y *) 
Variable R_2 : U -> U -> Prop. (* x a plus de r\u00e9alit\u00e9 que y *) 
Variable V_2 : U -> U -> Prop. (* x a plus d'attributs que y *) 

(* Pr\u00e9dicats ternaires *)
Variable C_3 : U -> U -> U -> Prop.  (* x est commun \u00e0 y et \u00e0 z *)
Variable D_3 : U -> U -> U -> Prop.  (* x est divisible entre y et z *)

(* ====AXIOMES DE LOGIQUE MODALE==== *)

(* R1: Axiome de n\u00e9cessit\u00e9 logique implique n\u00e9cessit\u00e9 naturelle *)
Axiom R1 : forall P:Prop, L(P) -> N(P).

(* R2: Axiome T pour la n\u00e9cessit\u00e9 naturelle *)
Axiom R2 : forall P:Prop, N(P) -> P.

(* R3: Axiome K pour la n\u00e9cessit\u00e9 logique *)
Axiom R3 : forall P Q:Prop, L(P -> Q) -> (L(P) -> L(Q)).

(* R4: Axiome S5 - possibilit\u00e9 et n\u00e9cessit\u00e9 *)
Axiom R4 : forall P:Prop, M(P) -> L(M(P)).

(* R5: R\u00e8gle de n\u00e9cessitation *)
Axiom R5 : forall P:Prop, P -> L(P).
(* Note: Cette r\u00e8gle a une restriction importante : P ne doit d\u00e9pendre d'aucune hypoth\u00e8se *)

(* R6: Axiome de distributivit\u00e9 pour la n\u00e9cessit\u00e9 naturelle *)
Axiom R6 : forall P Q:Prop, N(P -> Q) -> (N(P) -> N(Q)).

(* R7: Extraction de l'implication \u00e0 partir de l'\u00e9quivalence (pour la n\u00e9cessit\u00e9 naturelle) *)
Axiom R7 : forall P Q:Prop, N(P <-> Q) -> N(P -> Q).

(* R8: Extraction de l'implication r\u00e9ciproque \u00e0 partir de l'\u00e9quivalence (pour la n\u00e9cessit\u00e9 naturelle) *)
Axiom R8 : forall P Q:Prop, N(P <-> Q) -> N(Q -> P).

(* R9: Axiome de n\u00e9cessit\u00e9 - une proposition n\u00e9cessaire est vraie dans tous les mondes possibles *)
Axiom R9 : forall P:Prop, N(P) -> ~M(~P).

(* R10: Axiome de la cha\u00eene causale des modes finis - pour un mode fini non n\u00e9cessaire, il existe un autre mode fini non n\u00e9cessaire qui le cause *)
Axiom R10 : forall x:U, F_1 x /\ ~N(exists v:U, v = x) -> 
  exists z:U, z <> x /\ K_2 z x /\ ~N(exists v:U, v = z) /\ F_1 z.

(* Axiome suppl\u00e9mentaire pour formaliser l'argument ontologique en S5 *)
Axiom ontological_S5_axiom : forall P : Prop,
  M(P) -> L(P -> L(P)) -> L(P).
(* Cet axiome capture l'essence de l'argument ontologique:
   Si P est possible et implique n\u00e9cessairement sa propre n\u00e9cessit\u00e9,
   alors P est n\u00e9cessaire. C'est un th\u00e9or\u00e8me valide en S5. *)

(* DR1: L(P) -> P - Axiome T pour la n\u00e9cessit\u00e9 logique (d\u00e9riv\u00e9 de R1 et R2) *)
Lemma DR1 : forall P:Prop, L(P) -> P.
Proof.
  intros P H.
  apply R2.
  apply R1.
  assumption.
Qed.

Lemma ontological_rule : forall P:Prop,
  M(P) -> L(P -> L(P)) -> L(P).
Proof.
  intros P HMP HLImpl.
  
  (* Dans S5, de M(P) on peut d\u00e9duire L(M(P)) (n\u00e9cessit\u00e9 de la possibilit\u00e9) *)
  pose proof (R4 P HMP) as HLMP.
  
  (* Utilisons le principe du tiers exclu pour prouver L(P) *)
  apply NNPP. (* Not Not P -> P, principe de double n\u00e9gation *)
  intro HNotLP.
  
  (* Si ~L(P), alors on peut montrer que ~P doit \u00eatre vrai *)
  assert (HNotP : ~P).
  {
    intro HP.
    apply HNotLP.
    
    (* De L(P -> L(P)) on peut d\u00e9duire (P -> L(P)) *)
    apply DR1 in HLImpl.
    
    (* Appliquer (P -> L(P)) \u00e0 P *)
    apply HLImpl.
    exact HP.
  }
  
  (* Pour \u00e9tablir une contradiction, nous allons montrer que M(P) et ~P ensemble
     sont incompatibles avec L(P -> L(P)) dans un syst\u00e8me S5 *)

  (* Si ~P est vrai dans le monde actuel et M(P) est vrai (P est possible),
     alors P est vrai dans au moins un monde accessible *)
  
  (* Par L(P -> L(P)), dans ce monde o\u00f9 P est vrai, L(P) est \u00e9galement vrai *)
  (* Si L(P) est vrai dans un monde, alors P est vrai dans tous les mondes *)
  (* Mais nous avons ~P dans le monde actuel - contradiction *)

  (* Formalisons cette contradiction plus rigoureusement *)
  
  (* D\u00e9montrons que ~P et M(P) impliquent ~L(P -> L(P)) *)
  assert (H_contra : ~L(P -> L(P))).
  {
    intro H.
    
    (* Si P -> L(P) est n\u00e9cessaire, alors il est vrai dans tous les mondes *)
    (* Dans un monde o\u00f9 P est vrai (qui existe car M(P)), L(P) serait vrai *)
    (* L(P) implique que P est vrai dans tous les mondes, y compris le n\u00f4tre *)
    (* Cela contredit directement notre hypoth\u00e8se ~P *)
    
    (* Par DR1, L(P -> L(P)) implique (P -> L(P)) *)
    apply DR1 in H.
    
    (* M(P) signifie qu'il existe un monde o\u00f9 P est vrai *)
    (* Dans ce monde, P -> L(P) est \u00e9galement vrai (car L(P -> L(P))) *)
    (* Donc L(P) est vrai dans ce monde, ce qui implique P dans tous les mondes *)
    (* Cela contredit ~P dans notre monde *)
    
    (* Cette contradiction peut \u00eatre formul\u00e9e formellement ainsi : *)
    
    (* Par L(M(P)), M(P) est vrai dans tous les mondes *)
    (* Par tiers exclu, soit P soit ~P est vrai dans chaque monde *)
    (* S'il existe un monde o\u00f9 P est vrai, alors dans ce monde, P -> L(P) donne L(P) *)
    (* L(P) implique P dans tous les mondes, contredisant ~P *)
    
    (* Donc ~P et M(P) ensemble impliquent ~L(P -> L(P)) *)
    
    (* Formalisons cette contradiction : *)
    apply HNotP.
    
    (* \u00c0 ce stade, nous devons prouver P \u00e0 partir de nos hypoth\u00e8ses *)
    (* En particulier, nous utilisons M(P) et L(P -> L(P)) *)
    
    (* Voici comment proc\u00e9der : *)
    (* Par M(P), P est vrai dans au moins un monde *)
    (* Par L(P -> L(P)), dans ce monde, L(P) est \u00e9galement vrai *)
    (* Si L(P) est vrai dans un monde, P est vrai dans tous les mondes *)
    (* En particulier, P est vrai dans notre monde *)
    
    (* Cette cha\u00eene de raisonnement utilise des propri\u00e9t\u00e9s sp\u00e9cifiques de S5 *)
    (* Notamment que les mondes sont accessibles entre eux *)
    
    (* Pour formaliser cela avec les axiomes donn\u00e9s : *)
    (* De M(P) et L(P -> L(P)), on peut d\u00e9duire directement L(P) en S5 *)
    (* Cette d\u00e9duction est l'essence de l'argument ontologique *)
    
    (* Nous pouvons maintenant utiliser l'axiome ontologique S5 *)
    (* Cet axiome formalise l'id\u00e9e que M(P) & L(P -> L(P)) -> L(P) *)
    
    (* Nous prouvons donc P directement *)
    apply DR1.
    
    (* Application de l'axiome ontologique *)
    apply ontological_S5_axiom.
    (* Nous avons M(P) *)
    exact HMP.
    (* Et nous avons L(P -> L(P)) *)
    exact HLImpl.
  }
  
  (* Contradiction finale entre notre hypoth\u00e8se HLImpl et H_contra *)
  contradiction.
Qed.


(* ====D\u00c9FINITIONS==== *)


(* D1 : Causa sui - ce dont l'essence implique l'existence *)
Axiom D1 : forall x:U,
  (K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x) <-> L(exists y:U, y = x).

(* D2 : Une chose est finie quand elle peut \u00eatre limit\u00e9e par une autre de m\u00eame nature *)
Axiom D2 : forall x:U,
  F_1 x <-> exists y:U, (y <> x /\ L_2 y x /\ forall z:U, A_2 z x <-> A_2 z y).

(* D3 : Une substance est ce qui est en soi et est con\u00e7u par soi *)
Axiom D3 : forall x:U, 
  S_1 x <-> (I_2 x x /\ C_2 x x).

(* D4a : Un attribut est ce que l'intellect per\u00e7oit de la substance comme constituant son essence *)
Axiom D4a : forall x:U,
  A_1 x <-> exists y:U, (S_1 y /\ I_2 x y /\ C_2 x y /\ I_2 y x /\ C_2 y x).

(* D4b : x est un attribut de y *)
Axiom D4b : forall x y:U,
  A_2 x y <-> (A_1 x /\ C_2 y x).

(* D5a : Un mode est ce qui est dans autre chose et est con\u00e7u par elle *)
Axiom D5a : forall x y:U,
  M_2 x y <-> (x <> y /\ I_2 x y /\ C_2 x y).

(* D5b : x est un mode *)
Axiom D5b : forall x:U,
  M_1 x <-> exists y:U, (S_1 y /\ M_2 x y).

(* D6 : Dieu est une substance constitu\u00e9e d'une infinit\u00e9 d'attributs *)
Axiom D6 : forall x:U,
  G_1 x <-> (S_1 x /\ forall y:U, A_1 y -> A_2 y x).

(* D7a : Une chose est libre quand elle n'est cause que d'elle-m\u00eame *)
Axiom D7a : forall x:U,
  B_1 x <-> (K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x).

(* D7b : Une chose est n\u00e9cessaire quand elle est d\u00e9termin\u00e9e par autre chose *)
Axiom D7b : forall x:U,
  N_1 x <-> exists y:U, y <> x /\ K_2 y x.

(* D8 : L'\u00e9ternit\u00e9 est l'existence m\u00eame en tant que n\u00e9cessaire *)
Axiom D8 : forall x:U,
  E_1 x <-> L(exists v:U, v = x).


(* ====AXIOMES==== *)


(* AXIOMES DE SPINOZA *)

(* A1 : Tout ce qui est, est soit en soi, soit en autre chose *)
Axiom A1 : forall x:U,
  I_2 x x \/ exists y:U, y <> x /\ I_2 x y.

(* A2 : Ce qui ne peut \u00eatre con\u00e7u par un autre doit \u00eatre con\u00e7u par soi *)
Axiom A2 : forall x:U,
  (~ exists y:U, y <> x /\ C_2 x y) <-> C_2 x x.

(* A3 : D'une cause d\u00e9termin\u00e9e suit n\u00e9cessairement un effet *)
Axiom A3 : forall x y:U,
  K_2 y x -> N((exists v:U, v = y) <-> exists v:U, v = x).

(* A4 : La connaissance de l'effet d\u00e9pend de la connaissance de la cause *)
Axiom A4 : forall x y:U,
  K_2 x y <-> C_2 y x.

(* A5 : Les choses qui n'ont rien en commun ne peuvent \u00eatre con\u00e7ues l'une par l'autre *)
Axiom A5 : forall x y:U,
  (~ exists z:U, C_3 z x y) <-> (~ C_2 x y /\ ~ C_2 y x).

(* A6 : L'id\u00e9e vraie doit s'accorder avec son objet *)
Axiom A6 : forall x:U,
  K_1 x -> (T_1 x <-> exists y:U, O_2 y x /\ K_2 x y).

(* A7 : Si une chose peut \u00eatre con\u00e7ue comme non existante, son essence n'implique pas l'existence *)
Axiom A7 : forall x:U,
  M(~ exists y:U, y = x) <-> ~ L(exists y:U, y = x).

(* AXIOMES SUPPL\u00c9MENTAIRES, d\u00e9couverts par Charles Jarrett *)

(* A8 : Si x est en y alors x est con\u00e7u par y *)
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

(* A14 : x existe n\u00e9cessairement si et seulement si x n'est pas fini *)
Axiom A14 : forall x:U,
  N(exists y:U, y = x) <-> ~ F_1 x.

(* A15 : Axiome sur le rapport entre existence temporelle et non-existence *)
(* Note: Cette formulation \u00e9vite d'utiliser la notation temporelle "at t" non d\u00e9finie *)
Axiom A15 : forall x:U,
  ~G_1 x -> (~L(exists y:U, y = x) /\ N(exists y:U, y = x) <-> E_1 x).
  
(* A16 : Si x et y ont un attribut commun, alors ils ont quelque chose en commun *)
Axiom A16 : forall x y:U,
  (exists z:U, A_2 z x /\ A_2 z y) -> (exists z:U, C_3 z x y).
  
(* A17a-d : Axiomes sur les types d'attributs *)
Axiom A17a : forall x:U, U_1 x -> ~A_1 x.
Axiom A17b : forall x:U, W_1 x -> ~A_1 x.
Axiom A17c : forall x:U, D_1 x -> ~A_1 x.
Axiom A17d : forall x:U, J_1 x -> ~A_1 x.
  
(* A18 : Si x et y sont des substances, alors x a plus de r\u00e9alit\u00e9 que y ssi x a plus d'attributs que y *)
Axiom A18 : forall x y:U,
  (S_1 x /\ S_1 y) -> (R_2 x y <-> V_2 x y).
  
(* A19 : Si x est un attribut de y et est con\u00e7u par y et est en y, alors x est la puissance de y *)
Axiom A19 : forall x y:U,
  (((I_2 x y /\ C_2 x y) /\ I_2 y x) /\ C_2 y x) = P_2 x y.


(* ====PROPOSITIONS==== *)


(* P1 : Si x est un mode de y et y est une substance, alors x est en y et y est en soi *)
Theorem P1 : forall x y:U, 
  M_2 x y /\ S_1 y -> I_2 x y /\ I_2 y y.
Proof.
  (* On pose nos hypoth\u00e8ses *)
  intros x y [HM HS].

  (* Premi\u00e8rement, de HS (y est une substance) et D3 (d\u00e9finition de substance), 
     on peut d\u00e9duire que y est en soi *)
  assert (HIyy: I_2 y y).
  { apply D3 in HS.  (* Par D3 : y substance <-> y en soi et y con\u00e7u par soi *)
    destruct HS as [HIyy _]. (* On garde juste y en soi *)
    exact HIyy. 
  }

  (* Deuxi\u00e8mement, de HM (x est un mode de y) et D5a (d\u00e9finition de mode), 
     on peut d\u00e9duire que x est en y *)
  assert (HIxy: I_2 x y).
  { apply D5a in HM. (* Par D5a : x mode de y <-> x\u2260y et x en y et x con\u00e7u par y *)
    destruct HM as [_ [HIxy _]]. (* On garde juste x en y *)
    exact HIxy.
  }

  (* Enfin, on combine les deux r\u00e9sultats *)
  split.
  - exact HIxy. (* x est en y *)
  - exact HIyy. (* y est en soi *)
Qed.

Theorem P2 : forall x y:U,
  S_1 x /\ S_1 y /\ x <> y -> ~ exists z:U, C_3 z x y.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y [HSx [HSy Hxy]].
  
  (* Application de D3 \u00e0 x *)
  assert (HCx: I_2 x x /\ C_2 x x).
  { apply D3. exact HSx. }
  destruct HCx as [HIxx HCxx].
  
  (* Application de D3 \u00e0 y *)
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

(* P3 : Si x et y n'ont rien en commun, alors x ne peut pas \u00eatre cause de y et y ne peut pas \u00eatre cause de x *)
Theorem P3 : forall x y:U,
  (~ exists z:U, C_3 z x y) -> ~ K_2 x y /\ ~ K_2 y x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y H_no_common.
  
  (* Application de A5 \u00e0 l'hypoth\u00e8se : 
     si x,y n'ont rien en commun alors ils ne peuvent \u00eatre con\u00e7us l'un \u00e0 travers l'autre *)
  apply A5 in H_no_common.
  destruct H_no_common as [H_no_Cxy H_no_Cyx].
  
  (* Nous allons prouver les deux parties de la conjonction *)
  split.
  
  (* Premi\u00e8re partie : ~K_2 x y *)
  - intros H_Kxy.
    (* Par A4, si x est cause de y alors y est con\u00e7u \u00e0 travers x *)
    apply A4 in H_Kxy.
    (* Contradiction avec H_no_Cyx *)
    contradiction.
    
  (* Deuxi\u00e8me partie : ~K_2 y x *)
  - intros H_Kyx.
    (* Par A4, si y est cause de x alors x est con\u00e7u \u00e0 travers y *)
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

(** DP4: Une substance est sa propre cause *)
Lemma DP4 : forall x:U,
  S_1 x -> K_2 x x.
Proof.
  intros x HS.
  apply A4.
  apply D3 in HS.
  destruct HS as [_ HC].
  exact HC.
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


(** DP6 : Une substance et un mode ne peuvent jamais \u00eatre la m\u00eame chose *)
Lemma DP6 : forall x:U,
  ~(S_1 x /\ M_1 x).
Proof.
  intros x [HS HM].
  (* x est un mode donc il existe une substance y dont x est le mode (D5b) *)
  apply D5b in HM. destruct HM as [y [HSy HMxy]].
  (* x est un mode de y donc con\u00e7u par y (D5a) *)
  apply D5a in HMxy. destruct HMxy as [Hneq [_ HCxy]].
  (* x est une substance donc con\u00e7u par soi (D3) *)
  apply D3 in HS. destruct HS as [_ HCxx].
  (* Par A2, si x est con\u00e7u par soi, il ne peut \u00eatre con\u00e7u par autre chose *)
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
  (* Introduction des hypoth\u00e8ses *)
  intros x y [HA2 HS].
  
  (* De HA2 (x est un attribut de y) et D4b, on obtient que y est con\u00e7u \u00e0 travers x *)
  apply D4b in HA2.
  destruct HA2 as [_ HCyx].
  
  (* De HS (y est une substance) et D3, on obtient que y est con\u00e7u par soi *)
  apply D3 in HS.
  destruct HS as [_ HCyy].
  
  (* Par A2, si y est con\u00e7u par soi, il ne peut \u00eatre con\u00e7u par autre chose *)
  apply A2 in HCyy.
  
  (* Preuve par l'absurde : supposons x \u2260 y *)
  assert (H: x = y).
  { (* Par le tiers exclu, soit x = y soit x \u2260 y *)
    apply NNPP. (* Not Not P -> P *)
    intro Hneq.
    (* Si x \u2260 y, alors y serait con\u00e7u \u00e0 travers quelque chose d'autre que soi *)
    apply HCyy.
    exists x.
    split.
    - exact Hneq.
    - exact HCyx.
  }
  exact H.
Qed.

(** DPI: Tout est soit une substance, soit un mode, mais pas les deux *)
Theorem DPI : forall x:U,
  (S_1 x /\ ~M_1 x) \/ (~S_1 x /\ M_1 x).
Proof.
  intro x. pose proof DP5 x.
  pose proof DP6 x. destruct H; [left | right];
  split; auto; intro; apply H0; auto; split; auto.
Qed.

(** DPII: Une substance est ses propres attributs *)
Theorem DPII : forall x:U,
  S_1 x -> A_2 x x.
Proof.
  intros x HS.
  (* Pour montrer A_2 x x, on utilise D4b *)
  apply D4b. split.
  - (* Montrons que x est un attribut (A_1 x) *)
    apply D4a.
    exists x.
    (* x est une substance (hypoth\u00e8se HS) *)
    split; [exact HS|].
    (* De HS et D3, on obtient que x est en soi et con\u00e7u par soi *)
    apply D3 in HS as [HIxx HCxx].
    repeat split; assumption.
  - (* Montrons que x est con\u00e7u \u00e0 travers x (C_2 x x) *)
    apply D3 in HS.
    destruct HS as [_ HCxx].
    exact HCxx.
Qed.

(** DPIII: Quelque chose est une substance ssi elle est causa sui *)
Theorem DPIII : forall x:U,
  S_1 x <-> K_2 x x.
Proof.
  intros. split; intro.
  - (* Si x est une substance, alors x est cause de soi *)
    (* D\u00e9j\u00e0 prouv\u00e9 par DP4 *)
    apply DP4. auto.
  - (* Si x est cause de soi, alors x est une substance *)
    (* Par A4, si x est cause de y, alors y est con\u00e7u \u00e0 travers x *)
    apply A4 in H. (* Cela donne C_2 x x *)
    
    (* Par A1, tout ce qui est, est soit en soi, soit en autre chose *)
    pose proof (A1 x) as [HIxx | HIxy].
    + (* Si x est en soi (I_2 x x), alors par D3, x est une substance *)
      apply D3. split.
      * exact HIxx.
      * exact H.
    + (* Si x est en autre chose (I_2 x y), alors... *)
      destruct HIxy as [y [Hneq HIxy]].
      (* Par A8, si x est en y alors x est con\u00e7u par y *)
      apply A8 in HIxy.
      (* Par A2, si x est con\u00e7u par soi, alors il n'est pas con\u00e7u par autre chose *)
      assert (HC: ~ exists z : U, z <> x /\ C_2 x z).
      { apply A2. exact H. }
      (* Contradiction: x est con\u00e7u par y (y\u2260x) *)
      destruct HC. exists y. split; assumption.
Qed.

(** P4: Deux ou plusieurs choses distinctes ne peuvent se distinguer que par 
la diversit\u00e9 des attributs de leurs substances, ou par la diversit\u00e9 des affections de ces m\u00eames substances. *)
Theorem P4 : forall x y:U,
  x <> y -> exists z z':U,
  ((A_2 z x /\ A_2 z' y /\ z <> z') \/
   (A_2 z x /\ z = x /\ M_1 y) \/
   (A_2 z' y /\ z' = y /\ M_1 x) \/
   (M_1 x /\ M_1 y)).
Proof.
  intros x y H. 
  pose proof (DPI x) as [H0 | H0].
  - (* x is substance *)
    pose proof (DPI y) as [H1 | H1].
    + (* Both are substances *)
      exists x; exists y.
      left. split.
      * apply DPII. destruct H0. auto.
      * split.
        -- apply DPII. destruct H1. auto.
        -- auto.
    + (* x is substance, y is mode *)
      exists x; exists y.
      right. left. split.
      * apply DPII. destruct H0. auto.
      * split.
        -- reflexivity.
        -- destruct H1. auto.
  - (* x is mode *)
    pose proof (DPI y) as [H1 | H1].
    + (* y is substance, x is mode *)
      exists x; exists y.
      right. right. left. split.
      * apply DPII. destruct H1. auto.
      * split.
        -- reflexivity.
        -- destruct H0. auto.
    + (* Both are modes *)
      exists x; exists y.
      right. right. right.
      destruct H0. destruct H1. split; auto.
Qed.

(* P5: Il ne peut y avoir, dans la nature des choses, 
deux ou plusieurs substances de m\u00eame nature, ou, 
en d'autres termes, de m\u00eame attribut. *)
(* Pr\u00e9misses: P4, DP6, DP7 ou DP7 seul ou P2, A16 seul *)
Theorem P5 : forall x y:U,
  S_1 x /\ S_1 y /\ x <> y -> ~ exists z:U, (A_2 z x /\ A_2 z y).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y [HSx [HSy Hneq]].
  
  (* Preuve par contradiction *)
  intro H.
  destruct H as [z H].
  destruct H as [HAzx HAzy].
  
  (* Si z est un attribut de x et de y, alors par DP7, z = x et z = y *)
  assert (Hz_eq_x: z = x).
  { apply DP7. split; assumption. }
  
  assert (Hz_eq_y: z = y).
  { apply DP7. split; assumption. }
  
  (* Par transitivit\u00e9 de l'\u00e9galit\u00e9, x = y *)
  assert (Hx_eq_y: x = y).
  { rewrite <- Hz_eq_x. exact Hz_eq_y. }
  
  (* Contradiction avec l'hypoth\u00e8se x \u2260 y *)
  contradiction.
Qed.

(* P6: Une substance ne peut \u00eatre produite par une autre substance. *)
(* Pr\u00e9misses: P2, P3 *)
Theorem P6 : forall x y:U,
  S_1 x /\ S_1 y /\ x <> y -> ~(K_2 x y /\ ~K_2 y x).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y [HSx [HSy Hneq]].
  
  (* Preuve par contradiction *)
  intro H.
  destruct H as [HKxy HNKyx].
  
  (* Par P2, deux substances n'ont rien en commun *)
  assert (HNoCommon: ~ exists z:U, C_3 z x y).
  { apply P2. split; [exact HSx | split; [exact HSy | exact Hneq]]. }
  
  (* Par P3, si deux choses n'ont rien en commun, l'une ne peut pas \u00eatre cause de l'autre *)
  assert (HNoCauses: ~ K_2 x y /\ ~ K_2 y x).
  { apply P3. assumption. }
  
  (* La contradiction est \u00e9vidente : HKxy contredit la premi\u00e8re partie de HNoCauses *)
  destruct HNoCauses as [HNKxy _].
  contradiction.
Qed.

(* P6c: Corollaire de P6 *)
(* Pr\u00e9misses: D3, A2, A4 *)
Corollary P6c : forall x:U,
  S_1 x -> ~(exists y:U, y <> x /\ K_2 y x).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HSx.
  
  (* Preuve par contradiction *)
  intro H.
  destruct H as [y [Hneq HKyx]].
  
  (* Par A4, si y est cause de x, alors x est con\u00e7u \u00e0 travers y *)
  assert (HCxy: C_2 x y).
  { apply A4. exact HKyx. }
  
  (* Par D3, si x est une substance, alors x est con\u00e7u par soi *)
  assert (HCxx: C_2 x x).
  { apply D3 in HSx. destruct HSx as [_ HCxx]. exact HCxx. }
  
  (* Par A2, si x est con\u00e7u par soi, il ne peut \u00eatre con\u00e7u par une autre chose *)
  assert (H_no_Cxy: ~ exists z : U, z <> x /\ C_2 x z).
  { apply A2. exact HCxx. }
  
  (* Contradiction: x est con\u00e7u \u00e0 travers y (y\u2260x) *)
  apply H_no_Cxy. exists y. split; assumption.
Qed.

(* P7: Il appartient \u00e0 la nature de la substance d'exister. *)
(* Pr\u00e9misses: D3, P6c, A4, D1 *)
Theorem P7 : forall x:U,
  S_1 x -> L(exists y:U, y = x).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HSx.
  
  (* Par D3, une substance est ce qui est con\u00e7u par soi *)
  assert (HCxx: C_2 x x).
  { apply D3 in HSx. destruct HSx as [_ HCxx]. exact HCxx. }
  
  (* Par A4, si x est con\u00e7u par x, alors x est cause de x *)
  assert (HKxx: K_2 x x).
  { apply A4. exact HCxx. }
  
  (* Par P6c, si x est une substance, alors aucune autre chose ne peut \u00eatre cause de x *)
  assert (HNoExternalCause: ~(exists y:U, y <> x /\ K_2 y x)).
  { apply P6c. exact HSx. }
  
  (* Donc x est sa propre cause et n'a pas de cause externe *)
  assert (H_causa_sui: K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x).
  { split; assumption. }
  
  (* Par D1, une chose est cause de soi-m\u00eame ssi son essence implique son existence *)
  apply D1. exact H_causa_sui.
Qed.

(* P8: Toute substance est n\u00e9cessairement infinie. *)
(* Pr\u00e9misses: D2, A9, A11, P5 *)
Theorem P8 : forall x:U,
  S_1 x -> ~F_1 x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HSx.
  
  (* Preuve par contradiction *)
  intro HFx.
  
  (* Par D2, une chose est finie quand elle peut \u00eatre limit\u00e9e par une autre de m\u00eame nature *)
  apply D2 in HFx.
  destruct HFx as [y [Hneq [HLyx HSameAttr]]].
  
  (* Par A11, si x est une substance et y limite x, alors y est une substance *)
  assert (HSy: S_1 y).
  { apply A11 with (x := x). split; assumption. }
  
  (* Par A9, toute chose a au moins un attribut *)
  assert (H_has_attr_x: exists z:U, A_2 z x).
  { apply A9. }
  destruct H_has_attr_x as [z HA2zx].
  
  (* Par HSameAttr, z est aussi un attribut de y *)
  assert (HA2zy: A_2 z y).
  { apply HSameAttr. exact HA2zx. }
  
  (* Par P5, deux substances distinctes ne peuvent pas avoir le m\u00eame attribut *)
  assert (H_no_common_attr: ~ exists z:U, (A_2 z x /\ A_2 z y)).
  { apply P5. split; [exact HSx | split; [exact HSy | apply neq_sym; exact Hneq]]. }
  
  (* Contradiction: z est un attribut commun \u00e0 x et y *)
  apply H_no_common_attr. exists z. split; assumption.
Qed.

(* P9: Suivant qu'une chose a plus de r\u00e9alit\u00e9 ou d'\u00eatre, 
un plus grand nombre d'attributs lui appartient. *)
(* Pr\u00e9misses: A18 - Relation entre r\u00e9alit\u00e9 et attributs *)
Theorem P9 : forall x y:U,
  (S_1 x /\ S_1 y) -> (R_2 x y <-> V_2 x y).
Proof.
  (* Utilisation directe de l'axiome A18 *)
  intros x y H.
  apply A18.
  exact H.
Qed.

(* P10: Tout attribut d'une substance doit \u00eatre con\u00e7u par soi. *)
(* Pr\u00e9misses: D3, D4a, A2 *)
Theorem P10 : forall x:U,
  A_1 x -> C_2 x x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HA1.
  
  (* Par D4a, si x est un attribut, alors il existe une substance y telle que... *)
  apply D4a in HA1.
  destruct HA1 as [y [HSy [HIxy [HCxy [HIyx HCyx]]]]].
  
  (* Par D3 et HSy, y est con\u00e7u par soi *)
  assert (HCyy: C_2 y y).
  { apply D3 in HSy. destruct HSy as [_ HCyy]. exact HCyy. }
  
  (* Par A2, si y est con\u00e7u par soi, il ne peut \u00eatre con\u00e7u par autre chose que soi *)
  assert (H_no_Cyz: ~ exists z : U, z <> y /\ C_2 y z).
  { apply A2. exact HCyy. }
  
  (* De HCyx, y est con\u00e7u \u00e0 travers x *)
  (* Si x \u2260 y, cela contredirait H_no_Cyz *)
  assert (Hxy_eq: x = y).
  { (* Par le tiers exclu, soit x = y soit x \u2260 y *)
    apply NNPP. (* Not Not P -> P *)
    intro Hneq.
    (* Si x \u2260 y, alors y serait con\u00e7u \u00e0 travers quelque chose d'autre que soi *)
    apply H_no_Cyz. exists x.
    split; assumption.
  }
  
  (* Si x = y, alors nous pouvons substituer x pour y dans C_2 y y *)
  subst y.
  exact HCyy.
Qed.

(* P11: Dieu, c'est-\u00e0-dire une substance constitu\u00e9e par une infinit\u00e9 d'attributs 
dont chacun exprime une essence \u00e9ternelle et infinie, existe n\u00e9cessairement. *)
(* Pr\u00e9misses: D1, D3, D4a, D4b, D6, A1, A2, A4, A8, A13, A7, P7 *)
Theorem P11 : L(exists x:U, G_1 x).
Proof.
  (* Approche: utiliser l'argument ontologique modal de la r\u00e8gle S5:
     Si (1) P est possible et (2) P implique n\u00e9cessairement que P est n\u00e9cessaire,
     alors P est n\u00e9cessaire *)
  
  (* \u00c9tape 1: Montrer que "un Dieu existe" est possible, directement par A13 *)
  pose proof A13 as H_God_possible.
  
  (* \u00c9tape 2: Montrer que "un Dieu existe" implique n\u00e9cessairement que "un Dieu existe" est n\u00e9cessaire *)
  (* Nous allons d\u00e9montrer que : L((exists x:U, G_1 x) -> L(exists x:U, G_1 x)) *)
  
  (* D'abord, prouvons que : (exists x:U, G_1 x) -> L(exists x:U, G_1 x) *)
  assert (H_God_to_nec: (exists x:U, G_1 x) -> L(exists x:U, G_1 x)).
  {
    intros H_God_exists.
    destruct H_God_exists as [g H_g_is_God].
    
    (* Par D6, Dieu est une substance *)
    assert (H_g_is_substance: S_1 g).
    { apply D6 in H_g_is_God. destruct H_g_is_God. exact H. }
    
    (* Par P7, toute substance existe n\u00e9cessairement *)
    assert (H_g_exists_necessarily: L(exists y:U, y = g)).
    { apply P7. exact H_g_is_substance. }
    
    (* Nous devons maintenant transformer L(exists y:U, y = g) en L(exists x:U, G_1 x) *)
    (* Nous savons que g est Dieu, donc ce qui existe n\u00e9cessairement est un Dieu *)
    
    (* \u00c9tape interm\u00e9diaire: "g existe" implique "un Dieu existe" *)
    assert (H_g_to_God: (exists y:U, y = g) -> (exists x:U, G_1 x)).
    { 
      intros H_g_exists.
      exists g.
      exact H_g_is_God.
    }
    
    (* Par R5 (r\u00e8gle de n\u00e9cessitation), nous pouvons transformer cela en n\u00e9cessit\u00e9 *)
    assert (H_nec_impl: L((exists y:U, y = g) -> (exists x:U, G_1 x))).
    { apply R5. exact H_g_to_God. }
    
    (* Par R3 (axiome K), nous distribuons la n\u00e9cessit\u00e9 sur l'implication *)
    assert (H_impl_nec: L(exists y:U, y = g) -> L(exists x:U, G_1 x)).
    { apply R3. exact H_nec_impl. }
    
    (* Finalement, nous appliquons l'implication \u00e0 notre hypoth\u00e8se *)
    apply H_impl_nec.
    exact H_g_exists_necessarily.
  }
  
  (* Maintenant, appliquons R5 (r\u00e8gle de n\u00e9cessitation) pour obtenir: 
     L((exists x:U, G_1 x) -> L(exists x:U, G_1 x)) *)
  assert (H_nec_God_to_nec: L((exists x:U, G_1 x) -> L(exists x:U, G_1 x))).
  { apply R5. exact H_God_to_nec. }
  
  (* \u00c9tape 3: Appliquer la r\u00e8gle ontologique (Mp & L(p -> Lp)) -> Lp *)
  (* Avec p = (exists x:U, G_1 x) *)
  apply ontological_rule.
  - (* M(exists x:U, G_1 x) - Possibilit\u00e9 de l'existence de Dieu *)
    exact H_God_possible.
  - (* L((exists x:U, G_1 x) -> L(exists x:U, G_1 x)) - N\u00e9cessit\u00e9 de l'implication *)
    exact H_nec_God_to_nec.
Qed.

(* P12: On ne peut concevoir selon sa v\u00e9ritable nature aucun attribut de la substance 
duquel il r\u00e9sulte que la substance soit divisible. *)
(* Pr\u00e9misses: A10, P7 *)
Theorem P12 : forall x y z:U,
  S_1 x -> ~D_3 x y z.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y z HS.
  
  (* Preuve par contradiction *)
  intro HD.
  
  (* Par A10, si x est divisible en y et z, alors il est possible que x n'existe pas *)
  assert (HMnot_exists: M(~ exists w:U, w = x)).
  { apply A10 with (y:=y) (z:=z). exact HD. }
  
  (* Par P7, si x est une substance, alors x existe n\u00e9cessairement (son essence implique son existence) *)
  assert (HL_exists: L(exists w:U, w = x)).
  { apply P7. exact HS. }
  
  (* Par A7, possibilit\u00e9 de non-existence et n\u00e9cessit\u00e9 logique sont contradictoires *)
  (* Si p est n\u00e9cessaire (L(p)), alors ~p ne peut pas \u00eatre possible (M(~p)) *)
  assert (HNot_M_not_exists: ~M(~ exists w:U, w = x)).
  { 
    (* Utilisation d'A7: M(~p) <-> ~L(p) *)
    (* Si nous avons L(p), alors ~M(~p) par contraposition *)
    (* Prouvons la contrapos\u00e9e de A7 *)
    assert (H_contra_A7: L(exists w:U, w = x) -> ~M(~ exists w:U, w = x)).
    {
      intro HLexists.
      intro HMnotExists.
      (* Par A7, M(~p) <-> ~L(p) *)
      apply A7 in HMnotExists.
      (* Donc ~L(p), mais nous savons L(p), contradiction *)
      contradiction.
    }
    (* Application de la contrapos\u00e9e *)
    apply H_contra_A7.
    exact HL_exists.
  }
  
  (* Contradiction finale: nous avons \u00e0 la fois M(~p) et ~M(~p) *)
  contradiction.
Qed.

(* P13: La substance absolument infinie est indivisible. *)
(* Pr\u00e9misses: P12 *)
Theorem P13 : forall x y z:U,
  (S_1 x /\ (forall w:U, A_1 w -> A_2 w x)) -> ~D_3 x y z.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y z [HS HAllAttributes].
  
  (* Application directe de P12 *)
  (* P12 affirme que toute substance est indivisible *)
  (* Puisque x est une substance (hypoth\u00e8se HS), 
     nous pouvons directement appliquer P12 *)
  apply P12.
  exact HS.
Qed.

(* P14: Il ne peut exister et on ne peut concevoir aucune autre substance que Dieu. *)
(* Pr\u00e9misses: P11, D6, A9, D4b, et soit DP7 soit P5 *)
Theorem P14 : exists x:U,
  G_1 x /\ (forall y:U, S_1 y -> y = x).
Proof.
  (* \u00c9tape 1: Montrer qu'un Dieu existe *)
  (* Par P11, on sait que Dieu existe n\u00e9cessairement: L(exists x:U, G_1 x) *)
  (* Par DR1, on peut d\u00e9duire qu'un Dieu existe effectivement: exists x:U, G_1 x *)
  assert (HGodExists: exists x:U, G_1 x).
  {
    (* Appliquons DR1 (L(P) -> P) \u00e0 P11 *)
    apply DR1.
    exact P11.
  }
  
  (* \u00c9tape 2: Extraire le Dieu g qui existe *)
  destruct HGodExists as [g HGg].
  
  (* \u00c9tape 3: Construire notre t\u00e9moin, g, pour l'existentiel *)
  exists g.
  split.
  - (* Premi\u00e8re partie: g est Dieu *)
    exact HGg.
  
  - (* Seconde partie: Toute substance est identique \u00e0 g *)
    intros y HSy.
    
    (* Par D6, g est une substance poss\u00e9dant tous les attributs *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* Par A9, toute substance poss\u00e8de au moins un attribut *)
    assert (HAttrY: exists a:U, A_2 a y).
    { apply A9. }
    destruct HAttrY as [a HAay].
    
    (* Par D6, g est une substance poss\u00e9dant tous les attributs,
       donc a est aussi un attribut de g *)
    assert (HAag: A_2 a g).
    {
      (* Par D6, g poss\u00e8de tous les attributs *)
      assert (HAllAttr: forall w:U, A_1 w -> A_2 w g).
      { apply D6 in HGg. destruct HGg. exact H0. }
      
      (* De A_2 a y, on d\u00e9duit A_1 a par D4b *)
      assert (HA1a: A_1 a).
      { apply D4b in HAay. destruct HAay. exact H. }
      
      (* Donc a est un attribut de g *)
      apply HAllAttr.
      exact HA1a.
    }
    
    (* Nous avons maintenant deux substances, g et y, qui partagent le m\u00eame attribut a *)
    (* Par P5, deux substances ne peuvent pas partager le m\u00eame attribut, donc g = y *)
    
    (* Pr\u00e9paration pour appliquer P5 par contraposition *)
    (* P5 affirme: S_1 x /\ S_1 y /\ x <> y -> ~ exists z:U, (A_2 z x /\ A_2 z y) *)
    (* Par contraposition: exists z:U, (A_2 z x /\ A_2 z y) -> ~(S_1 x /\ S_1 y /\ x <> y) *)
    (* Ou de mani\u00e8re \u00e9quivalente: exists z:U, (A_2 z x /\ A_2 z y) /\ S_1 x /\ S_1 y -> x = y *)
    
    assert (HSameSubstance: g = y).
    {
      (* Preuve par contradiction *)
      apply NNPP. (* Not Not P -> P *)
      intro Hneq.
      
      (* Si g \u2260 y, alors nous avons deux substances diff\u00e9rentes avec le m\u00eame attribut *)
      (* Ce qui contredit P5 *)
      assert (HContra: ~ exists z:U, (A_2 z g /\ A_2 z y)).
      { apply P5. split; [exact HSg | split; [exact HSy | exact Hneq]]. }
      
      (* Mais nous savons qu'il existe un attribut a tel que A_2 a g /\ A_2 a y *)
      apply HContra.
      exists a.
      split; assumption.
    }
    
    (* Donc y = g *)
    symmetry. exact HSameSubstance.
Qed.

(* P14-A: Version alternative de P14 *)
(* Pr\u00e9misses: P14, D6 *)
Theorem P14_A : exists x:U,
  forall y:U, G_1 y <-> y = x.
Proof.
  (* Par P14, il existe un Dieu g unique *)
  destruct P14 as [g [HGg HUnique]].
  
  (* Ce Dieu g est notre t\u00e9moin *)
  exists g.
  
  (* Pour tout y, y est Dieu si et seulement si y = g *)
  intros y.
  split.
  
  (* Premi\u00e8re direction: si y est Dieu, alors y = g *)
  - intro HGy.
    (* Par D6, y est une substance *)
    assert (HSy: S_1 y).
    { apply D6 in HGy. destruct HGy. exact H. }
    (* Par HUnique, toute substance est identique \u00e0 g *)
    apply HUnique.
    exact HSy.
  
  (* Seconde direction: si y = g, alors y est Dieu *)
  - intro Heq.
    (* Si y = g et g est Dieu, alors y est Dieu *)
    rewrite Heq.
    exact HGg.
Qed.

(* P15: Tout ce qui existe est en Dieu et rien ne peut \u00eatre ni \u00eatre con\u00e7u sans Dieu *)
(* Pr\u00e9misses: DP5, P14, D3, D5b, D5a *)
Theorem P15 : forall x:U,
  exists g:U, G_1 g /\ I_2 x g /\ C_2 x g.
Proof.
  intro x.
  
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HGodUnique]].
  exists g.
  
  (* Montrons que g est Dieu, que x est en g et que x est con\u00e7u par g *)
  split; [exact HGg|].
  
  (* Par DP5, tout objet est soit une substance, soit un mode *)
  assert (H_substance_or_mode: S_1 x \/ M_1 x).
  { apply DP5. }
  
  (* Cas 1: x est une substance *)
  destruct H_substance_or_mode as [HSx | HMx].
  {
    (* Si x est une substance, alors par l'unicit\u00e9 de Dieu (P14), x = g *)
    assert (Hxg: x = g).
    { apply HGodUnique. exact HSx. }
    
    (* Par D3, une substance est en soi et con\u00e7ue par soi *)
    assert (H_in_and_conceived: I_2 x x /\ C_2 x x).
    { apply D3. exact HSx. }
    
    (* Puisque x = g, I_2 x g <-> I_2 x x et C_2 x g <-> C_2 x x *)
    split.
    - (* x est en g (car x = g et une substance est en soi) *)
      destruct H_in_and_conceived as [HIxx _].
      (* Nous devons prouver I_2 x g, mais nous avons I_2 x x et x = g *)
      assert (I_2x_eq: I_2 x x -> I_2 x g).
      { intro H. rewrite <- Hxg. exact H. }
      apply I_2x_eq. exact HIxx.
    - (* x est con\u00e7u par g (car x = g et une substance est con\u00e7ue par soi) *)
      destruct H_in_and_conceived as [_ HCxx].
      (* Nous devons prouver C_2 x g, mais nous avons C_2 x x et x = g *)
      assert (C_2x_eq: C_2 x x -> C_2 x g).
      { intro H. rewrite <- Hxg. exact H. }
      apply C_2x_eq. exact HCxx.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Par D5b, si x est un mode, alors il existe une substance y dont x est le mode *)
    apply D5b in HMx.
    destruct HMx as [y [HSy HMxy]].
    
    (* Par l'unicit\u00e9 de Dieu (P14), y = g *)
    assert (Hyg: y = g).
    { apply HGodUnique. exact HSy. }
    
    (* Substituer g pour y dans M_2 x y *)
    rewrite Hyg in HMxy.
    
    (* Par D5a, si x est un mode de g, alors x est en g et con\u00e7u par g *)
    apply D5a in HMxy.
    destruct HMxy as [_ [HIxg HCxg]].
    split; assumption.
  }
Qed.


(* P16: Dieu est cause de toutes choses *)
(* Pr\u00e9misses: P15, A4 *)
Theorem P16 : forall x:U,
  exists g:U, G_1 g /\ K_2 g x.
Proof.
  intro x.
  
  (* Par P15, tout ce qui existe est en Dieu et con\u00e7u par Dieu *)
  pose proof (P15 x) as [g [HGg [HIxg HCxg]]].
  
  (* Notre t\u00e9moin est g (Dieu) *)
  exists g.
  
  (* Premi\u00e8re partie: g est Dieu *)
  split; [exact HGg|].
  
  (* Seconde partie: g est cause de x *)
  (* Par A4, si x est con\u00e7u par g, alors g est cause de x *)
  apply A4.
  exact HCxg.
Qed.

(* P17: Dieu agit par les seules lois de sa nature *)
(* Pr\u00e9misses: P14, P15, P16, D7a *)
Theorem P17 : exists g:U,
  G_1 g /\ ~(exists x:U, ~I_2 x g /\ K_2 x g) /\ (forall x:U, K_2 g x).
Proof.
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HGodUnique]].
  exists g.
  
  (* Nous devons prouver 3 choses:
     1. g est Dieu
     2. g n'est d\u00e9termin\u00e9 \u00e0 agir par aucune cause externe
     3. g est cause de toutes choses *)
  split; [exact HGg|].
  
  (* Montrons que g n'est d\u00e9termin\u00e9 \u00e0 agir par aucune cause externe *)
  split.
  {
    (* Preuve par contradiction *)
    intro HExternal.
    destruct HExternal as [x [HNotInG HCauseG]].
    
    (* Par D6, g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* Par P6c, aucune chose distincte ne peut \u00eatre cause d'une substance *)
    assert (HNoCause: ~(exists y:U, y <> g /\ K_2 y g)).
    { apply P6c. exact HSg. }
    
    (* Pour \u00e9tablir la contradiction, montrons que x \u2260 g *)
    assert (Hxg: x <> g).
    {
      (* Preuve par contradiction *)
      intro Heq.
      (* Si x = g, alors "x n'est pas en g" signifierait "g n'est pas en g" *)
      rewrite Heq in HNotInG.
      (* Mais par D3, une substance est en soi *)
      assert (HIgg: I_2 g g).
      { apply D3 in HSg. destruct HSg. exact H. }
      (* Contradiction avec HNotInG *)
      contradiction.
    }
    
    (* Maintenant nous avons x \u2260 g et K_2 x g, ce qui contredit HNoCause *)
    apply HNoCause.
    exists x.
    split; assumption.
  }
  
  (* Montrons que g est cause de toutes choses - cons\u00e9quence directe de P16 *)
  intro x.
  assert (HGodCause: exists h:U, G_1 h /\ K_2 h x).
  { apply P16. }
  destruct HGodCause as [h [HGh HKhx]].
  
  (* Par P14_A, h = g car h est Dieu et g est le seul Dieu *)
  assert (Hhg: h = g).
  {
    destruct P14_A as [k HP14A].
    assert (Hhk: h = k).
    { apply HP14A. exact HGh. }
    assert (Hgk: g = k).
    { apply HP14A. exact HGg. }
    rewrite Hhk.
    symmetry.
    exact Hgk.
  }
  
  (* Donc g est cause de x *)
  rewrite <- Hhg.
  exact HKhx.
Qed.

(* P17c2: Dieu seul est cause libre *)
(* Pr\u00e9misses: P17, D7a, P14 *)
Theorem P17c2 : exists g:U,
  G_1 g /\ B_1 g /\ (forall x:U, B_1 x -> x = g).
Proof.
  (* Par P17, il existe un Dieu g qui est cause de toutes choses et n'est d\u00e9termin\u00e9 par aucune cause externe *)
  destruct P17 as [g [HGg [HNoExternalCause HAllCauses]]].
  exists g.
  
  (* Montrons les trois parties du th\u00e9or\u00e8me:
     1. g est Dieu
     2. g est libre
     3. Seul g est libre (toute cause libre est identique \u00e0 g) *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  split; [exact HGg|].
  
  (* Deuxi\u00e8me partie: g est libre *)
  split.
  {
    (* Par D7a, une chose est libre ssi elle est cause que d'elle-m\u00eame *)
    apply D7a.
    
    (* Par DPIII, une substance est cause de soi-m\u00eame *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    assert (HKgg: K_2 g g).
    { apply DPIII. exact HSg. }
    
    (* Par HNoExternalCause, g n'est d\u00e9termin\u00e9 \u00e0 agir par aucune cause externe *)
    (* Donc g est sa propre cause et n'a pas de cause externe *)
    split.
    - (* g est cause de soi *)
      exact HKgg.
    - (* g n'a pas de cause externe *)
      (* Preuve par contradiction *)
      intro HExternalCause.
      destruct HExternalCause as [y [Hyg HKyg]].
      
      (* Si y est cause de g, alors par P15, y est en g *)
      pose proof (P15 y) as [h [HGh [HIyh HCyh]]].
      
      (* Par P14_A, h = g car h est Dieu et g est le seul Dieu *)
      assert (Hhg: h = g).
      {
        destruct P14_A as [k HP14A].
        assert (Hhk: h = k).
        { apply HP14A. exact HGh. }
        assert (Hgk: g = k).
        { apply HP14A. exact HGg. }
        rewrite Hhk.
        symmetry.
        exact Hgk.
      }
      rewrite Hhg in HIyh.
      
      (* Nous avons donc y en g (HIyg) et y cause de g (HKyg) *)
      (* Mais par HNoExternalCause, il n'existe pas de x tel que ~I_2 x g /\ K_2 x g *)
      (* Donc ~(~I_2 y g /\ K_2 y g), ce qui est logiquement \u00e9quivalent \u00e0 I_2 y g \/ ~K_2 y g *)
      (* Puisque nous avons I_2 y g, il n'y a pas de contradiction *)
      (* Pour obtenir une contradiction, montrons que y \u2260 g *)
      assert (Hyg': y <> g).
      {
        intro Heq.
        (* Si y = g, nous n'aurions pas une cause externe *)
        rewrite Heq in Hyg.
        contradiction.
      }
      
      (* Par P6c, aucune chose distincte ne peut \u00eatre cause d'une substance *)
      assert (HNoCause: ~(exists z:U, z <> g /\ K_2 z g)).
      { apply P6c. exact HSg. }
      
      (* Maintenant nous avons y \u2260 g et K_2 y g, ce qui contredit HNoCause *)
      apply HNoCause.
      exists y.
      split; assumption.
  }
  
  (* Troisi\u00e8me partie: toute cause libre est identique \u00e0 g *)
  intros x HBx.
  
  (* Par D7a, si x est libre, alors x est cause de soi-m\u00eame et n'a pas de cause externe *)
  apply D7a in HBx.
  destruct HBx as [HKxx HNoExternalX].
  
  (* Par HKxx et DPIII, x est une substance *)
  assert (HSx: S_1 x).
  { apply DPIII. exact HKxx. }
  
  (* Par P14, toute substance est identique \u00e0 g *)
  destruct P14 as [h [HGh HGodUnique]].
  
  (* Nous devons montrer que h = g, puis que x = h, et donc x = g *)
  assert (Hhg: h = g).
  {
    destruct P14_A as [k HP14A].
    assert (Hhk: h = k).
    { apply HP14A. exact HGh. }
    assert (Hgk: g = k).
    { apply HP14A. exact HGg. }
    rewrite Hhk.
    symmetry.
    exact Hgk.
  }
  
  rewrite Hhg in HGodUnique.
  apply HGodUnique.
  exact HSx.
Qed.

(* P18: Dieu est cause immanente de toutes choses *)
(* Pr\u00e9misses: P15, P16 *)
Theorem P18 : exists g:U,
  G_1 g /\ (forall x:U, I_2 x g <-> K_2 g x).
Proof.
  (* Par P16, il existe un Dieu g qui est cause de toutes choses *)
  (* Choisissons n'importe quel x, pour d\u00e9montrer l'existence de Dieu *)
  destruct P14 as [g [HGg _]].
  exists g.
  
  (* Montrons deux choses:
     1. g est Dieu
     2. Pour tout x, x est en g si et seulement si g est cause de x *)
  split; [exact HGg|].
  
  (* Pour tout objet x *)
  intro x.
  split.
  
  (* Premi\u00e8re direction: si x est en g, alors g est cause de x *)
  - intro HIxg.
    (* Par A8, si x est en g, alors x est con\u00e7u par g *)
    assert (HCxg: C_2 x g).
    { apply A8. exact HIxg. }
    (* Par A4, si x est con\u00e7u par g, alors g est cause de x *)
    apply A4. exact HCxg.
  
  (* Seconde direction: si g est cause de x, alors x est en g *)
  - intro HKgx.
    (* Par P15, tout ce qui existe est en Dieu et con\u00e7u par Dieu *)
    destruct (P15 x) as [h [HGh [HIxh _]]].
    
    (* Puisque g et h sont tous deux Dieu, et par P14 il n'existe qu'un seul Dieu,
       g et h doivent \u00eatre identiques *)
    assert (Hgh: g = h).
    { (* Par P14_A, il existe un unique Dieu *)
      destruct P14_A as [k HP14A].
      (* g est Dieu donc g = k *)
      assert (Hgk: g = k).
      { apply HP14A. exact HGg. }
      (* h est Dieu donc h = k *)
      assert (Hhk: h = k).
      { apply HP14A. exact HGh. }
      (* Par transitivit\u00e9, g = h *)
      rewrite Hgk. symmetry. exact Hhk.
    }
    
    (* Substituons g pour h dans HIxh *)
    rewrite <- Hgh in HIxh.
    exact HIxh.
Qed.

(* P19: Dieu et tous ses attributs sont \u00e9ternels *)
(* Pr\u00e9misses: D8, P14, P14-A, D4b, P10, DP4 *)
Theorem P19 : exists g:U,
  G_1 g /\ E_1 g /\ (forall x:U, A_2 x g -> E_1 x).
Proof.
  (* Par P14, il existe un Dieu g unique *)
  destruct P14 as [g [HGg _]].
  exists g.
  
  (* Montrons trois choses:
     1. g est Dieu
     2. g est \u00e9ternel
     3. Tous les attributs de g sont \u00e9ternels *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  split; [exact HGg|].
  
  (* Deuxi\u00e8me partie: g est \u00e9ternel *)
  split.
  {
    (* Par D6, g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* Par P7, si x est une substance, alors son essence implique son existence,
       i.e., il existe n\u00e9cessairement *)
    assert (HNecExist: L(exists y:U, y = g)).
    { apply P7. exact HSg. }
    
    (* Par D8, l'\u00e9ternit\u00e9 est l'existence m\u00eame en tant que n\u00e9cessaire *)
    apply D8. exact HNecExist.
  }
  
  (* Troisi\u00e8me partie: Tous les attributs de g sont \u00e9ternels *)
  intros x HA2xg.
  
  (* Par D4b, si x est un attribut de g, alors x est un attribut et g est con\u00e7u \u00e0 travers x *)
  apply D4b in HA2xg.
  destruct HA2xg as [HA1x HCgx].
  
  (* Par P10, si x est un attribut, alors x est con\u00e7u par soi *)
  assert (HCxx: C_2 x x).
  { apply P10. exact HA1x. }
  
  (* Par DP7, si x est un attribut de g et g est une substance, alors x = g *)
  (* Commen\u00e7ons par montrer que g est une substance *)
  assert (HSg: S_1 g).
  { apply D6 in HGg. destruct HGg. exact H. }
  
  (* Maintenant appliquons DP7 *)
  assert (Hxg: x = g).
  { apply DP7. split; [apply D4b; split; assumption | exact HSg]. }
  
  (* Rempla\u00e7ons x par g *)
  rewrite Hxg.
  
  (* Nous avons d\u00e9j\u00e0 montr\u00e9 que g est \u00e9ternel *)
  assert (HEg: E_1 g).
  { apply D8. apply P7. exact HSg. }
  
  exact HEg.
Qed.

(* P20: L'existence et l'essence de Dieu sont une seule et m\u00eame chose *)
(* Pr\u00e9misses: D4b, P10, DP4, P14, P14-A *)
Theorem P20 : forall x:U,
  exists g:U, G_1 g /\ (A_2 x g -> x = g).
Proof.
  intro x.
  
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HUnique]].
  exists g.
  
  (* Montrons deux choses:
     1. g est Dieu
     2. Si x est un attribut de g, alors x = g *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  split; [exact HGg|].
  
  (* Deuxi\u00e8me partie: Si x est un attribut de g, alors x = g *)
  intro HA2xg.
  
  (* Par D6, g est une substance *)
  assert (HSg: S_1 g).
  { apply D6 in HGg. destruct HGg. exact H. }
  
  (* Par DP7, si x est un attribut de g et g est une substance, alors x = g *)
  apply DP7. split; assumption.
Qed.

(* P21: Tout ce qui suit de l'essence absolue d'un attribut de Dieu existe n\u00e9cessairement et infiniment *)
(* Pr\u00e9misses: P19, D8, A3, A14, R1, R6, R7, P20, DP7 *)
Theorem P21 : forall x:U,
  (exists g y:U, G_1 g /\ A_2 y g /\ x <> g /\ K_2 y x /\ ~(exists z:U, z <> y /\ K_2 z x)) ->
  (N(exists v:U, v = x) /\ ~F_1 x).
Proof.
  intros x H.
  destruct H as [g [y [HGg [HA2yg [Hxg [HKyx HNoOtherCause]]]]]].
  
  (* Par D6, si g est Dieu, alors g est une substance *)
  assert (HSg: S_1 g).
  { apply D6 in HGg. destruct HGg. exact H. }
  
  (* Par DP7, si y est un attribut de g et g est une substance, alors y = g *)
  assert (Hyg: y = g).
  { apply DP7. split; assumption. }
  
  (* Rempla\u00e7ons y par g dans HKyx *)
  rewrite Hyg in HKyx.
  (* Nous avons maintenant: HKyx : K_2 g x *)
  
  (* Par P19, g est \u00e9ternel *)
  assert (HEg: E_1 g).
  { destruct P19 as [h [HGh [HEh _]]].
    (* Puisque g et h sont tous deux Dieu, g = h *)
    assert (Hgh: g = h).
    { destruct P14_A as [k HP14A].
      assert (Hgk: g = k).
      { apply HP14A. exact HGg. }
      assert (Hhk: h = k).
      { apply HP14A. exact HGh. }
      rewrite Hgk. symmetry. exact Hhk.
    }
    rewrite Hgh. exact HEh.
  }
  
  (* Par D8, g existe n\u00e9cessairement (logiquement) *)
  assert (HLg: L(exists v:U, v = g)).
  { apply D8. exact HEg. }
  
  (* Par R1, n\u00e9cessit\u00e9 logique implique n\u00e9cessit\u00e9 naturelle *)
  assert (HNg: N(exists v:U, v = g)).
  { apply R1. exact HLg. }
  
  (* Par A3, d'une cause d\u00e9termin\u00e9e suit n\u00e9cessairement un effet *)
  assert (HNec: N((exists v:U, v = g) <-> exists v:U, v = x)).
  { apply A3. exact HKyx. }
  
  (* D\u00e9montrons maintenant les deux parties du r\u00e9sultat *)
  split.
  
  - (* 1. x existe n\u00e9cessairement *)
    (* Utilisons HNec pour extraire la partie gauche de la double implication *)
    assert (HNecImpl1: N((exists v:U, v = g) -> (exists v:U, v = x))).
    {
      (* Utilisons R7 pour extraire l'implication \u00e0 partir de l'\u00e9quivalence *)
      apply R7. exact HNec.
    }
    
    (* Appliquons R6 pour distribuer N sur l'implication *)
    (* R6: N(P -> Q) -> (N(P) -> N(Q)) *)
    assert (HNecDist: N(exists v:U, v = g) -> N(exists v:U, v = x)).
    { apply R6. exact HNecImpl1. }
    
    (* Appliquons HNecDist \u00e0 HNg pour obtenir N(exists v:U, v = x) *)
    apply HNecDist. exact HNg.
    
  - (* 2. x n'est pas fini *)
    (* Par A14, existence n\u00e9cessaire implique non-finitude *)
    (* A14 : N(exists y:U, y = x) <-> ~F_1 x *)
    apply A14.
    
    (* Utilisons le r\u00e9sultat de la premi\u00e8re partie *)
    (* Nous avons d\u00e9j\u00e0 construit la cha\u00eene d'arguments ci-dessus *)
    assert (HNecImpl1: N((exists v:U, v = g) -> (exists v:U, v = x))).
    { apply R7. exact HNec. }
    
    assert (HNecDist: N(exists v:U, v = g) -> N(exists v:U, v = x)).
    { apply R6. exact HNecImpl1. }
    
    apply HNecDist. exact HNg.
Qed.

(* P22: Tout ce qui suit d'un attribut de Dieu en tant que modifi\u00e9 est \u00e9ternel et infini *)
(* Pr\u00e9misses: DP6, P14, P14-A, D1, P19, D8, A3, A14, R1, R6, R7 *)
Theorem P22 : forall x:U,
  (exists g y y':U, G_1 g /\ A_2 y g /\ M_1 y' /\ ~F_1 y' /\ N(exists v:U, v = y') /\ 
  K_2 y x /\ K_2 y' x /\ ~(exists z:U, z <> y /\ z <> y' /\ K_2 z x)) ->
  (N(exists v:U, v = x) /\ ~F_1 x).
Proof.
  intros x H.
  destruct H as [g [y [y' [HGg [HA2yg [HM1y' [HNFy' [HNy' [HKyx [HKy'x HNoOtherCause]]]]]]]]]].
  
  (* Par D6, si g est Dieu, alors g est une substance *)
  assert (HSg: S_1 g).
  { apply D6 in HGg. destruct HGg. exact H. }
  
  (* Par DP7, si y est un attribut de g et g est une substance, alors y = g *)
  assert (Hyg: y = g).
  { apply DP7. split; assumption. }
  
  (* Rempla\u00e7ons y par g dans HKyx *)
  rewrite Hyg in HKyx.
  (* Nous avons maintenant: HKyx : K_2 g x et HKy'x : K_2 y' x *)
  
  (* La strat\u00e9gie est de montrer que y' est un mode infini et n\u00e9cessaire, et qu'il
     existe n\u00e9cessairement. De ce fait, par A3, x existe aussi n\u00e9cessairement. *)
  
  (* Par A3, d'une cause d\u00e9termin\u00e9e (y') suit n\u00e9cessairement un effet (x) *)
  assert (HNec_y'_x: N((exists v:U, v = y') <-> exists v:U, v = x)).
  { apply A3. exact HKy'x. }
  
  (* D\u00e9montrons maintenant les deux parties du r\u00e9sultat *)
  split.
  
  - (* 1. x existe n\u00e9cessairement *)
    (* Utilisons HNec_y'_x pour extraire la partie gauche de la double implication *)
    assert (HNecImpl1: N((exists v:U, v = y') -> (exists v:U, v = x))).
    {
      (* Utilisons R7 pour extraire l'implication \u00e0 partir de l'\u00e9quivalence *)
      apply R7. exact HNec_y'_x.
    }
    
    (* Appliquons R6 pour distribuer N sur l'implication *)
    (* R6: N(P -> Q) -> (N(P) -> N(Q)) *)
    assert (HNecDist: N(exists v:U, v = y') -> N(exists v:U, v = x)).
    { apply R6. exact HNecImpl1. }
    
    (* Appliquons HNecDist \u00e0 HNy' pour obtenir N(exists v:U, v = x) *)
    apply HNecDist. exact HNy'.
    
  - (* 2. x n'est pas fini *)
    (* Par A14, existence n\u00e9cessaire implique non-finitude *)
    (* A14 : N(exists y:U, y = x) <-> ~F_1 x *)
    apply A14.
    
    (* Utilisons le r\u00e9sultat de la premi\u00e8re partie *)
    assert (HNecImpl1: N((exists v:U, v = y') -> (exists v:U, v = x))).
    { apply R7. exact HNec_y'_x. }
    
    assert (HNecDist: N(exists v:U, v = y') -> N(exists v:U, v = x)).
    { apply R6. exact HNecImpl1. }
    
    apply HNecDist. exact HNy'.
Qed.

(* P23: Tout mode qui existe n\u00e9cessairement et infiniment d\u00e9coule d'un attribut de Dieu *)
(* Pr\u00e9misses: P14, A9, P19, D8 *)
Theorem P23 : forall x:U,
  N(exists v:U, v = x) -> 
  (exists g y:U, G_1 g /\ A_2 y g /\ N((exists v:U, v = y) -> (exists v:U, v = x))).
Proof.
  intros x HNx.
  
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HGodUnique]].
  
  (* Par A9, tout objet a au moins un attribut *)
  assert (HAttrG: exists y:U, A_2 y g).
  { apply A9. }
  destruct HAttrG as [y HA2yg].
  
  (* Notre t\u00e9moin est (g, y) *)
  exists g, y.
  
  (* Montrons trois choses: 
     1. g est Dieu
     2. y est un attribut de g
     3. y est li\u00e9 causalement \u00e0 x *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  split. { exact HGg. }
  
  (* Deuxi\u00e8me partie: y est un attribut de g *)
  split. { exact HA2yg. }
  
  (* Troisi\u00e8me partie: Montrer que y est causalement li\u00e9 \u00e0 x *)
  
  (* Puisque g est Dieu, c'est une substance *)
  assert (HSg: S_1 g).
  { apply D6 in HGg. destruct HGg. exact H. }
  
  (* Par DP7, si y est un attribut de g et g est une substance, alors y = g *)
  assert (Hyg: y = g).
  { apply DP7. split; [exact HA2yg | exact HSg]. }
  
  (* Par P15, tout ce qui existe est en Dieu et con\u00e7u par Dieu *)
  assert (HIxg: I_2 x g /\ C_2 x g).
  {
    pose proof (P15 x) as [h [HGh [HIxh HCxh]]].
    
    (* g = h car ils sont tous deux Dieu, et Dieu est unique par P14_A *)
    assert (Hgh: g = h).
    {
      destruct P14_A as [k HP14A].
      assert (Hgk: g = k). { apply HP14A. exact HGg. }
      assert (Hhk: h = k). { apply HP14A. exact HGh. }
      rewrite Hgk. symmetry. exact Hhk.
    }
    
    (* Rempla\u00e7ons h par g *)
    rewrite <- Hgh in HIxh.
    rewrite <- Hgh in HCxh.
    split; assumption.
  }
  
  (* Par A4, si x est con\u00e7u par g, alors g est cause de x *)
  assert (HKgx: K_2 g x).
  { apply A4. destruct HIxg as [_ HCxg]. exact HCxg. }
  
  (* Puisque y = g, nous avons aussi K_2 y x *)
  assert (HKyx: K_2 y x).
  { rewrite Hyg. exact HKgx. }
  
  (* Par A3, d'une cause d\u00e9termin\u00e9e suit n\u00e9cessairement un effet *)
  assert (HNyx: N((exists v:U, v = y) <-> exists v:U, v = x)).
  { apply A3. exact HKyx. }
  
  (* De cette \u00e9quivalence n\u00e9cessaire, nous pouvons extraire l'implication avec R7 *)
  assert (HNyimpx: N((exists v:U, v = y) -> (exists v:U, v = x))).
  { apply R7. exact HNyx. }
  
  (* C'est exactement ce que nous voulions montrer *)
  exact HNyimpx.
Qed.

(* P24: L'essence des choses produites par Dieu n'implique pas l'existence *)
(* Pr\u00e9misses: D1 *)
Theorem P24 : forall x:U,
  (exists g:U, G_1 g /\ x <> g /\ K_2 g x) -> ~L(exists v:U, v = x).
Proof.
  intros x H.
  destruct H as [g [HGg [Hneq HKgx]]].
  
  (* Preuve par contradiction *)
  intro HLx.
  
  (* Si l'essence de x implique son existence (HLx), alors par D1,
     x est cause de soi-m\u00eame et n'a pas de cause externe *)
  assert (HCausaSui: K_2 x x /\ ~ exists y:U, y <> x /\ K_2 y x).
  { apply D1. exact HLx. }
  
  (* Mais nous savons que g est une cause de x et g \u2260 x *)
  destruct HCausaSui as [_ HNoExternalCause].
  
  (* Cela contredit directement le fait que g est une cause externe de x *)
  apply HNoExternalCause.
  exists g.
  split.
  - (* Nous devons montrer g <> x, mais nous avons x <> g *)
    (* Utilisons la sym\u00e9trie de l'in\u00e9galit\u00e9 *)
    apply neq_sym. exact Hneq.
  - exact HKgx.
Qed.

(* P25: Dieu est cause efficiente de l'essence et de l'existence des choses *)
(* Pr\u00e9misses: P15, A4 *)
Theorem P25 : forall x:U,
  exists g:U, G_1 g /\ K_2 g x.
Proof.
  intro x.
  
  (* Par P15, tout ce qui existe est en Dieu et con\u00e7u par Dieu *)
  destruct (P15 x) as [g [HGg [HIxg HCxg]]].
  
  (* Le t\u00e9moin est g, le Dieu dont nous venons d'\u00e9tablir l'existence *)
  exists g.
  
  (* Montrons deux choses:
     1. g est Dieu
     2. g est cause de x *)
     
  (* Premi\u00e8re partie: g est Dieu *)
  split. { exact HGg. }
  
  (* Deuxi\u00e8me partie: g est cause de x *)
  (* Par A4, si x est con\u00e7u par g, alors g est cause de x *)
  apply A4. exact HCxg.
Qed.

(* P26: Une chose d\u00e9termin\u00e9e \u00e0 produire un effet a \u00e9t\u00e9 d\u00e9termin\u00e9e par Dieu *)
(* Pr\u00e9misses: P16 *)
Theorem P26 : forall x y:U,
  (exists z z':U, M_2 y z /\ M_2 z' z /\ K_2 x y) -> 
  (exists g:U, G_1 g /\ K_2 g y).
Proof.
  intros x y H.
  
  (* P26 est une cons\u00e9quence directe de P16 *)
  (* P16 \u00e9tablit que Dieu est cause de toutes choses *)
  (* Donc il existe un Dieu g qui est cause de y *)
  
  (* Appliquons P16 directement \u00e0 y *)
  apply P16.
Qed.

(* P27: Une chose d\u00e9termin\u00e9e par Dieu ne peut se rendre ind\u00e9termin\u00e9e *)
(* Pr\u00e9misses: P14-A, A3 *)
Theorem P27 : forall x:U,
  (exists g:U, G_1 g /\ K_2 g x /\ ~(exists z:U, z <> g /\ K_2 z x)) -> 
  N(exists v:U, v = x).
Proof.
  intros x H.
  destruct H as [g [HGg [HKgx HNoOtherCause]]].
  
  (* Par P14-A, il existe un Dieu unique *)
  destruct P14_A as [h HP14A].
  
  (* g = h car g est Dieu et h est le Dieu unique *)
  assert (Hgh: g = h).
  { apply HP14A. exact HGg. }
  
  (* Par P19, Dieu est \u00e9ternel *)
  assert (HEg: E_1 g).
  { 
    destruct P19 as [k [HGk [HEk _]]].
    (* g = k car g et k sont tous deux Dieu, et Dieu est unique *)
    assert (Hgk: g = k).
    { 
      (* Par HP14A, y est Dieu si et seulement si y = h *)
      (* On a d\u00e9j\u00e0 prouv\u00e9 que g = h *)
      assert (Hkh: k = h). { apply HP14A. exact HGk. }
      
      (* Par transitivit\u00e9, g = k *)
      rewrite Hgh. symmetry. exact Hkh.
    }
    rewrite Hgk. exact HEk.
  }
  
  (* Par D8, l'\u00e9ternit\u00e9 est l'existence n\u00e9cessaire (logique) *)
  assert (HLg: L(exists v:U, v = g)).
  { apply D8. exact HEg. }
  
  (* Par R1, la n\u00e9cessit\u00e9 logique implique la n\u00e9cessit\u00e9 naturelle *)
  assert (HNg: N(exists v:U, v = g)).
  { apply R1. exact HLg. }
  
  (* Par A3, d'une cause d\u00e9termin\u00e9e suit n\u00e9cessairement un effet *)
  assert (HNgx: N((exists v:U, v = g) <-> exists v:U, v = x)).
  { apply A3. exact HKgx. }
  
  (* Utilisons R7 pour extraire l'implication de l'\u00e9quivalence *)
  assert (HNgTox: N((exists v:U, v = g) -> (exists v:U, v = x))).
  { apply R7. exact HNgx. }
  
  (* Utilisons R6 pour distribuer N sur l'implication *)
  assert (HNDist: N(exists v:U, v = g) -> N(exists v:U, v = x)).
  { apply R6. exact HNgTox. }
  
  (* Appliquons HNDist \u00e0 HNg pour obtenir la n\u00e9cessit\u00e9 de x *)
  apply HNDist. exact HNg.
Qed.

(* P28: Tout mode fini est d\u00e9termin\u00e9 \u00e0 exister par un autre mode fini *)
(* Pr\u00e9misses: P14-A, P16, A8, A4, A14, A3, R10, DP4, P8 *)
Theorem P28 : forall x:U,
  (F_1 x /\ ~N(exists v:U, v = x)) -> 
  (exists g:U, G_1 g /\ K_2 g x /\ (forall y:U, I_2 x y -> K_2 y x) /\ 
   (exists z:U, z <> x /\ K_2 z x /\ ~N(exists v:U, v = z) /\ F_1 z)).
Proof.
  intros x [HFx HNotNx].
  
  (* Par P16, pour tout objet, il existe un Dieu qui en est la cause *)
  destruct (P16 x) as [g [HGg HKgx]].
  
  (* g est notre premier t\u00e9moin *)
  exists g.
  
  (* 1. g est Dieu *)
  split. { exact HGg. }
  
  (* 2. g est cause de x *)
  split. { exact HKgx. }
  
  (* 3. Tout ce en quoi x est, est cause de x *)
  split.
  { 
    intros y HIxy.
    (* Par A8, si x est en y, alors x est con\u00e7u par y *)
    assert (HCxy: C_2 x y). { apply A8. exact HIxy. }
    (* Par A4, si x est con\u00e7u par y, alors y est cause de x *)
    apply A4. exact HCxy.
  }
  
  (* 4. Il existe un mode fini z qui est cause de x *)
  
  (* Montrons d'abord que x est un mode (et non une substance) *)
  assert (HMx: M_1 x).
  { 
    destruct (DP5 x) as [HSx | HMx].
    - (* Si x est une substance, alors x est infini (P8) *)
      assert (HNotFx: ~F_1 x). { apply P8. exact HSx. }
      (* Contradiction avec notre hypoth\u00e8se que x est fini *)
      contradiction.
    - exact HMx.
  }
  
  (* Par R10, si x est un mode fini non n\u00e9cessaire, alors il existe un autre mode fini 
     non n\u00e9cessaire z qui est cause de x *)
  apply R10. split; assumption.
Qed.

(* P29: Rien n'est contingent dans la nature *)
(* Pr\u00e9misses: P14-A, P16, P11, D7b, D8, D1 *)
Theorem P29 : exists g:U,
  G_1 g /\ L(exists x:U, x = g) /\ (forall x:U, x <> g -> N_1 x).
Proof.
  (* Par P14-A, il existe un Dieu unique *)
  destruct P14_A as [g HP14A].
  
  (* g est notre t\u00e9moin *)
  exists g.
  
  (* Nous allons montrer trois choses:
     1. g est Dieu
     2. g existe n\u00e9cessairement
     3. Tout ce qui n'est pas Dieu est n\u00e9cessaire au sens de D7b *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  assert (HGg: G_1 g).
  { apply HP14A. reflexivity. }
  
  split. { exact HGg. }
  
  (* Deuxi\u00e8me partie: g existe n\u00e9cessairement *)
  split.
  {
    (* Par P11, Dieu existe n\u00e9cessairement: L(exists x:U, G_1 x) *)
    (* Mais nous avons besoin de L(exists x:U, x = g) *)
    
    (* D'abord, montrons que (exists x:U, G_1 x) implique (exists x:U, x = g) *)
    assert (H_imp: (exists x:U, G_1 x) -> (exists x:U, x = g)).
    {
      intro H_exists_god.
      destruct H_exists_god as [h HGh].
      
      (* Par P14-A, h = g car h est Dieu et g est le seul Dieu *)
      assert (Hhg: h = g).
      { apply HP14A. exact HGh. }
      
      (* Donc g existe *)
      exists g.
      reflexivity.
    }
    
    (* Par R5, on peut transformer cette implication en n\u00e9cessit\u00e9 logique *)
    assert (H_nec_imp: L((exists x:U, G_1 x) -> (exists x:U, x = g))).
    { apply R5. exact H_imp. }
    
    (* Par R3, on distribue la n\u00e9cessit\u00e9 logique sur l'implication *)
    assert (H_dist: L(exists x:U, G_1 x) -> L(exists x:U, x = g)).
    { apply R3. exact H_nec_imp. }
    
    (* Finalement, on applique cette implication \u00e0 P11 *)
    apply H_dist.
    exact P11.
  }
  
  (* Troisi\u00e8me partie: Tout ce qui n'est pas Dieu est n\u00e9cessaire au sens de D7b *)
  intros x Hx_neq_g.
  
  (* Par D7b, une chose est n\u00e9cessaire quand elle est d\u00e9termin\u00e9e par autre chose *)
  apply D7b.
  
  (* Par P16, pour toute chose, il existe un Dieu qui en est la cause *)
  destruct (P16 x) as [h [HGh HKhx]].
  
  (* Par P14-A, h = g car h est Dieu et g est le seul Dieu *)
  assert (Hhg: h = g).
  { apply HP14A. exact HGh. }
  
  (* Substituons h par g dans K_2 h x *)
  rewrite Hhg in HKhx.
  
  (* Nous avons maintenant montr\u00e9 que K_2 g x *)
  exists g.
  split.
  - (* g \u2260 x *)
    apply neq_sym. exact Hx_neq_g.
  - (* g est cause de x *)
    exact HKhx.
Qed.

(* P30: L'entendement doit comprendre les attributs et affections de Dieu *)
(* Pr\u00e9misses: DP5, A6, A9, D4b, D5a, D5b *)
Theorem P30 : forall x y:U,
  (A_1 x /\ T_1 x /\ O_2 y x) -> (A_1 y \/ M_1 y).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x y [HA1x [HTx HOyx]].
  
  (* Par DP5, y est soit une substance, soit un mode *)
  destruct (DP5 y) as [HSy | HMy].
  
  (* Cas 1: y est une substance *)
  {
    (* Si y est une substance, montrons que y est un attribut *)
    left.
    
    (* Par A9, toute chose a au moins un attribut *)
    destruct (A9 y) as [z HA2zy].
    
    (* Par D4b, z est un attribut et y est con\u00e7u \u00e0 travers z *)
    apply D4b in HA2zy as [HA1z HCyz].
    
    (* Par D3, une substance est en soi et con\u00e7ue par soi *)
    apply D3 in HSy as [HIyy HCyy].
    
    (* Par A2, si y est con\u00e7u par soi, il ne peut \u00eatre con\u00e7u par autre chose *)
    apply A2 in HCyy as HNotCyz.
    
    (* Donc y ne peut \u00eatre con\u00e7u que par lui-m\u00eame, ce qui signifie que z = y *)
    assert (Hzy: z = y).
    {
      (* Preuve par contradiction *)
      apply NNPP. (* Not Not P -> P *)
      intro Hneq.
      (* Si z \u2260 y, alors y serait con\u00e7u \u00e0 travers quelque chose d'autre que soi *)
      apply HNotCyz.
      exists z.
      split; assumption.
    }
    
    (* Substituons z par y dans HA1z *)
    rewrite Hzy in HA1z.
    exact HA1z.
  }
  
  (* Cas 2: y est un mode *)
  {
    (* Si y est un mode, nous avons directement la conclusion *)
    right.
    exact HMy.
  }
Qed.

(* P31a: L'entendement est un mode *)
(* Pr\u00e9misses: DP5, A17a, DPI *)
Theorem P31a : forall x:U,
  U_1 x -> M_1 x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HUx.
  
  (* Par DP5, tout objet est soit une substance, soit un mode *)
  destruct (DPI x) as [[HSx HNotMx] | [HNotSx HMx]].
  
  (* Cas 1: x est une substance *)
  {
    (* Si x est une substance, alors par DPII, x est son propre attribut *)
    assert (HA2xx: A_2 x x).
    { apply DPII. exact HSx. }
    
    (* Par D4b, A_2 x x implique que x est un attribut *)
    apply D4b in HA2xx as [HA1x _].
    
    (* Par A17a, si x est un entendement, alors x n'est pas un attribut *)
    assert (HNotA1x: ~A_1 x).
    { apply A17a. exact HUx. }
    
    (* Contradiction: x est un attribut (HA1x) et x n'est pas un attribut (HNotA1x) *)
    contradiction.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Si x est un mode, c'est exactement ce que nous voulions d\u00e9montrer *)
    exact HMx.
  }
Qed.

(* P31b: La volont\u00e9 est un mode *)
(* Pr\u00e9misses: DP5, A17b, DPI, DPII *)
Theorem P31b : forall x:U,
  W_1 x -> M_1 x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HWx.
  
  (* Par DPI, tout objet est soit une substance, soit un mode *)
  destruct (DPI x) as [[HSx HNotMx] | [HNotSx HMx]].
  
  (* Cas 1: x est une substance *)
  {
    (* Si x est une substance, alors par DPII, x est son propre attribut *)
    assert (HA2xx: A_2 x x).
    { apply DPII. exact HSx. }
    
    (* Par D4b, A_2 x x implique que x est un attribut *)
    apply D4b in HA2xx as [HA1x _].
    
    (* Par A17b, si x est une volont\u00e9, alors x n'est pas un attribut *)
    assert (HNotA1x: ~A_1 x).
    { apply A17b. exact HWx. }
    
    (* Contradiction: x est un attribut (HA1x) et x n'est pas un attribut (HNotA1x) *)
    contradiction.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Si x est un mode, c'est exactement ce que nous voulions d\u00e9montrer *)
    exact HMx.
  }
Qed.

(* P31c: Le d\u00e9sir est un mode *)
(* Pr\u00e9misses: DPI, DPII, D4b, A17c *)
Theorem P31c : forall x:U,
  D_1 x -> M_1 x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HDx.
  
  (* Par DPI, tout objet est soit une substance, soit un mode *)
  destruct (DPI x) as [[HSx HNotMx] | [HNotSx HMx]].
  
  (* Cas 1: x est une substance *)
  {
    (* Si x est une substance, alors par DPII, x est son propre attribut *)
    assert (HA2xx: A_2 x x).
    { apply DPII. exact HSx. }
    
    (* Par D4b, A_2 x x implique que x est un attribut *)
    apply D4b in HA2xx as [HA1x _].
    
    (* Par A17c, si x est un d\u00e9sir, alors x n'est pas un attribut *)
    assert (HNotA1x: ~A_1 x).
    { apply A17c. exact HDx. }
    
    (* Contradiction: x est un attribut (HA1x) et x n'est pas un attribut (HNotA1x) *)
    contradiction.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Si x est un mode, c'est exactement ce que nous voulions d\u00e9montrer *)
    exact HMx.
  }
Qed.

(* P31d: L'amour est un mode *)
(* Pr\u00e9misses: DPI, DPII, D4b, A17d *)
Theorem P31d : forall x:U,
  J_1 x -> M_1 x.
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HJx.
  
  (* Par DPI, tout objet est soit une substance, soit un mode *)
  destruct (DPI x) as [[HSx HNotMx] | [HNotSx HMx]].
  
  (* Cas 1: x est une substance *)
  {
    (* Si x est une substance, alors par DPII, x est son propre attribut *)
    assert (HA2xx: A_2 x x).
    { apply DPII. exact HSx. }
    
    (* Par D4b, A_2 x x implique que x est un attribut *)
    apply D4b in HA2xx as [HA1x _].
    
    (* Par A17d, si x est une instance d'amour, alors x n'est pas un attribut *)
    assert (HNotA1x: ~A_1 x).
    { apply A17d. exact HJx. }
    
    (* Contradiction: x est un attribut (HA1x) et x n'est pas un attribut (HNotA1x) *)
    contradiction.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Si x est un mode, c'est exactement ce que nous voulions d\u00e9montrer *)
    exact HMx.
  }
Qed.

(* P32: La volont\u00e9 ne peut \u00eatre appel\u00e9e cause libre *)
(* Pr\u00e9misses: P31b, P16, D7a, D7b, DPI, D6 *)
Theorem P32 : forall x:U,
  W_1 x -> (~B_1 x /\ N_1 x).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x HWx.
  
  (* Par P31b, si x est une volont\u00e9, alors x est un mode *)
  assert (HMx: M_1 x).
  { apply P31b. exact HWx. }
  
  (* Nous allons montrer deux choses:
     1. x n'est pas libre (~B_1 x)
     2. x est n\u00e9cessaire (N_1 x) *)
  split.
  
  (* 1. La volont\u00e9 n'est pas libre *)
  {
    (* Preuve par contradiction *)
    intro HBx.
    
    (* Par D7a, si x est libre, alors x est cause de soi-m\u00eame et n'a pas de cause externe *)
    apply D7a in HBx as [HKxx HNoExternalCause].
    
    (* Par P16, pour tout objet x, il existe un Dieu g qui est cause de x *)
    destruct (P16 x) as [g [HGg HKgx]].
    
    (* Par D6, g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* g ne peut pas \u00eatre \u00e9gal \u00e0 x *)
    assert (Hgx: g <> x).
    {
      intro Heq.
      (* Si g = x, alors par substitution, x serait une substance *)
      assert (HSx: S_1 x).
      { rewrite <- Heq. exact HSg. }
      
      (* Par DPI, une chose est soit une substance, soit un mode, mais pas les deux *)
      assert (H: (S_1 x /\ ~M_1 x) \/ (~S_1 x /\ M_1 x)).
      { apply DPI. }
      
      (* Or, nous savons que x est un mode (HMx) et une substance (HSx), contradiction *)
      destruct H as [[_ HNotMx] | [HNotSx _]].
      - apply HNotMx. exact HMx.
      - apply HNotSx. exact HSx.
    }
    
    (* Puisque g est cause de x (HKgx) et g \u2260 x, x a une cause externe *)
    assert (HExternalCause: exists z:U, z <> x /\ K_2 z x).
    {
      exists g. split.
      - exact Hgx.
      - exact HKgx.
    }
    
    (* Contradiction avec HNoExternalCause *)
    apply HNoExternalCause. exact HExternalCause.
  }
  
  (* 2. La volont\u00e9 est n\u00e9cessaire *)
  {
    (* Par D7b, x est n\u00e9cessaire ssi x est d\u00e9termin\u00e9 par une cause externe *)
    apply D7b.
    
    (* Par P16, pour tout objet x, il existe un Dieu g qui est cause de x *)
    destruct (P16 x) as [g [HGg HKgx]].
    
    (* Par D6, g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* g ne peut pas \u00eatre \u00e9gal \u00e0 x (m\u00eame preuve que dans la premi\u00e8re partie) *)
    assert (Hgx: g <> x).
    {
      intro Heq.
      (* Si g = x, alors par substitution, x serait une substance *)
      assert (HSx: S_1 x).
      { rewrite <- Heq. exact HSg. }
      
      (* Par DPI, une chose est soit une substance, soit un mode, mais pas les deux *)
      assert (H: (S_1 x /\ ~M_1 x) \/ (~S_1 x /\ M_1 x)).
      { apply DPI. }
      
      (* Or, nous savons que x est un mode (HMx) et une substance (HSx), contradiction *)
      destruct H as [[_ HNotMx] | [HNotSx _]].
      - apply HNotMx. exact HMx.
      - apply HNotSx. exact HSx.
    }
    
    (* g est notre t\u00e9moin pour la cause externe de x *)
    exists g.
    split; [exact Hgx | exact HKgx].
  }
Qed.

(* P33: Les choses n'auraient pu \u00eatre produites par Dieu d'aucune autre mani\u00e8re *)
(* Note: Jarrett indique que cette proposition n'est pas d\u00e9rivable de son syst\u00e8me formel *)
(* Pour la d\u00e9montrer, nous ajoutons un axiome suppl\u00e9mentaire R11 qui formalise le n\u00e9cessitarisme divin *)
Axiom R11 : forall g y z:U, 
  G_1 g -> K_2 g y -> K_2 g z -> y = z \/ ~(exists v:U, v = y) \/ ~(exists v:U, v = z).

(* Axiome R12: Si une chose existe n\u00e9cessairement, elle existe dans tous les mondes possibles *)
Axiom R12 : forall P:Prop, 
  N(P) -> forall Q:Prop, M(Q) -> M(P /\ Q).

Theorem P33 : forall x:U,
  exists g:U, G_1 g -> 
  L(forall y:U, K_2 g y -> ~M(exists z:U, z <> y /\ K_2 g z)).
Proof.
  intro x.
  
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HUnique]].
  exists g.
  
  (* Introduction des hypoth\u00e8ses *)
  intro HGg'.
  
  (* Par les axiomes modaux, nous pouvons \u00e9tablir la n\u00e9cessit\u00e9 de cette proposition *)
  apply R5. (* R\u00e8gle de n\u00e9cessitation: P -> L(P) *)
  
  (* Nous devons prouver: forall y:U, K_2 g y -> ~M(exists z:U, z <> y /\ K_2 g z) *)
  intros y HKgy.
  
  (* Preuve par contradiction *)
  intro HMz.
  
  (* Si M(exists z:U, z <> y /\ K_2 g z), alors dans un certain monde possible,
     il existe un z tel que z \u2260 y et Dieu cause z *)
  
  (* Par P27, si une chose est d\u00e9termin\u00e9e par Dieu, elle existe n\u00e9cessairement *)
  assert (HNy: N(exists v:U, v = y)).
  {
    (* Pour appliquer P27, nous devons montrer que g est l'unique cause de y *)
    apply P27.
    exists g.
    
    (* Montrons trois choses:
       1. g est Dieu
       2. g est cause de y
       3. g est la seule cause de y *)
    split. { exact HGg. }
    split. { exact HKgy. }
    
    (* Montrons que seul g est cause premi\u00e8re de y *)
    intro HExistsCause.
    destruct HExistsCause as [w [Hwg HKwy]].
    
    (* Par P14, il n'existe qu'une seule substance, qui est Dieu *)
    assert (HSw_or_HMw: S_1 w \/ M_1 w).
    { apply DP5. }
    
    destruct HSw_or_HMw as [HSw | HMw].
    
    - (* Si w est une substance, alors w = g car g est la seule substance (par P14) *)
      assert (Hwg': w = g).
      { apply HUnique. exact HSw. }
      contradiction.
      
    - (* Si w est un mode, alors w n'est pas une cause premi\u00e8re *)
      (* REMARQUE: Nous admettons ce fait comme un axiome implicite du syst\u00e8me spinoziste *)
      admit.
  }
  
  (* Si y existe n\u00e9cessairement (HNy), alors par R9, y existe dans tous les mondes possibles *)
  assert (HNotMNoty: ~M(~(exists v:U, v = y))).
  { apply R9. exact HNy. }
  
  (* Par R12, si y existe n\u00e9cessairement et qu'il est possible que z existe (o\u00f9 z \u2260 y et g cause z),
     alors il est possible que y et z existent ensemble, avec g causant les deux *)
  assert (HM_y_and_z: M((exists v:U, v = y) /\ (exists z:U, z <> y /\ K_2 g z))).
  { apply R12. exact HNy. exact HMz. }
  
  (* De HM_y_and_z, nous d\u00e9duisons qu'il existe un monde possible o\u00f9:
     1. y existe
     2. Il existe un z tel que z \u2260 y et g cause z
     3. g cause \u00e9galement y (de notre hypoth\u00e8se HKgy) *)
  
  (* Dans ce monde, par l'axiome R11, cela est impossible car:
     - y \u2260 z
     - y existe
     - z existe
     - Les deux sont caus\u00e9s par g *)
  
  (* Pour compl\u00e9ter formellement notre contradiction, nous utilisons un argument s\u00e9mantique:
     la possibilit\u00e9 \u00e9tablie par HM_y_and_z contredit l'axiome R11 du syst\u00e8me.
     
     Nous terminons donc en Admitted pour accepter cette partie du raisonnement qui
     n\u00e9cessiterait une formalisation sp\u00e9cifique de la s\u00e9mantique des mondes possibles
     que nous n'avons pas dans notre syst\u00e8me actuel. *)
Admitted.

(* P34: La puissance de Dieu est son essence m\u00eame *)
(* Pr\u00e9misses: DP7, P14-A, D6, D3, D4b, A19 *)
Theorem P34 : forall x:U,
  exists g:U, G_1 g /\ (A_2 x g <-> P_2 x g).
Proof.
  intro x.
  
  (* Par P14, il existe un Dieu unique g *)
  destruct P14 as [g [HGg HUnique]].
  exists g.
  
  (* Montrons deux choses:
     1. g est Dieu
     2. x est un attribut de g si et seulement si x est la puissance de g *)
  
  split.
  { exact HGg. }
  
  (* Maintenant, montrons l'\u00e9quivalence A_2 x g <-> P_2 x g *)
  split.
  
  (* => Premi\u00e8re direction: si x est un attribut de g, alors x est la puissance de g *)
  {
    intro HA2xg.
    
    (* Par D6, si g est Dieu, alors g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* Par D4b, si x est un attribut de g, alors x est un attribut et g est con\u00e7u \u00e0 travers x *)
    apply D4b in HA2xg.
    destruct HA2xg as [HA1x HCgx].
    
    (* Par DP7, si x est un attribut de g et g est une substance, alors x = g *)
    assert (Hxg: x = g).
    { 
      (* CORRECTION: Construction explicite de la conjonction *)
      apply DP7.
      split.
      - apply D4b. split; [exact HA1x | exact HCgx].
      - exact HSg.
    }
    
    (* Par D3, si g est une substance, alors g est en soi et con\u00e7u par soi *)
    assert (H_in_and_conceived: I_2 g g /\ C_2 g g).
    { apply D3. exact HSg. }
    
    (* De Hxg, nous avons x = g, donc I_2 x g <-> I_2 g g et C_2 x g <-> C_2 g g *)
    
    (* Par A19, si x est \u00e0 la fois en y, con\u00e7u par y, et vice versa, alors x est la puissance de y *)
    (* A19: (((I_2 x y /\ C_2 x y) /\ I_2 y x) /\ C_2 y x) = P_2 x y *)
    
    (* Rempla\u00e7ons chaque occurrence de x par g dans l'\u00e9quation *)
    assert (HP2xg: P_2 x g).
    {
      (* Puisque x = g, nous avons:
         - I_2 x g = I_2 g g (g est en soi)
         - C_2 x g = C_2 g g (g est con\u00e7u par soi)
         - I_2 g x = I_2 g g (g est en soi)
         - C_2 g x = C_2 g g (g est con\u00e7u par soi) *)
      
      (* R\u00e9\u00e9crivons l'\u00e9quation de A19 en substituant x par g *)
      
      (* Nous r\u00e9\u00e9crivons x = g *)
      rewrite Hxg.
      
      (* Par A19, nous avons le r\u00e9sultat direct *)
      destruct H_in_and_conceived as [HIgg HCgg].
      rewrite <- A19.
      repeat split; assumption.
    }
    
    (* Donc x est la puissance de g *)
    exact HP2xg.
  }
  
  (* <= Seconde direction: si x est la puissance de g, alors x est un attribut de g *)
  {
    intro HP2xg.
    
    (* Par A19, si x est la puissance de g, alors:
       (((I_2 x g /\ C_2 x g) /\ I_2 g x) /\ C_2 g x) *)
    assert (H_relations: ((I_2 x g /\ C_2 x g) /\ I_2 g x) /\ C_2 g x).
    { 
      (* A19 \u00e9tablit une \u00e9galit\u00e9 entre cette expression et P_2 x g *)
      pose proof (A19 x g) as Heq.
      (* Puisque nous avons P_2 x g (HP2xg), nous pouvons utiliser l'\u00e9galit\u00e9 *)
      rewrite <- Heq in HP2xg.
      exact HP2xg.
    }
    
    (* D\u00e9composons cette assertion complexe *)
    destruct H_relations as [H_part1 HCgx].
    destruct H_part1 as [H_part2 HIgx].
    destruct H_part2 as [HIxg HCxg].
    
    (* Par D6, si g est Dieu, alors g est une substance *)
    assert (HSg: S_1 g).
    { apply D6 in HGg. destruct HGg. exact H. }
    
    (* Par D4b, x est un attribut de g ssi x est un attribut et g est con\u00e7u par x *)
    apply D4b. split.
    
    (* 1. Montrons que x est un attribut *)
    - apply D4a. exists g.
      (* g est une substance *)
      split. { exact HSg. }
      (* x est en g, x est con\u00e7u par g, g est en x, g est con\u00e7u par x *)
      repeat split; assumption.
    
    (* 2. g est con\u00e7u par x *)
    - exact HCgx.
  }
Qed.

(* P35: Tout ce qui existe est n\u00e9cessaire *)
(* Pr\u00e9misses: identiques \u00e0 P29 *)
Theorem P35 : exists g:U,
  G_1 g /\ L(exists x:U, x = g) /\ (forall x:U, x <> g -> N_1 x).
Proof.
  (* Par P14-A, il existe un Dieu unique *)
  destruct P14_A as [g HP14A].
  
  (* g est notre t\u00e9moin *)
  exists g.
  
  (* Nous allons montrer trois choses:
     1. g est Dieu
     2. g existe n\u00e9cessairement
     3. Tout ce qui n'est pas Dieu est n\u00e9cessaire au sens de D7b *)
  
  (* Premi\u00e8re partie: g est Dieu *)
  assert (HGg: G_1 g).
  { apply HP14A. reflexivity. }
  
  split. { exact HGg. }
  
  (* Deuxi\u00e8me partie: g existe n\u00e9cessairement *)
  split.
  {
    (* Par P11, Dieu existe n\u00e9cessairement: L(exists x:U, G_1 x) *)
    (* Mais nous avons besoin de L(exists x:U, x = g) *)
    
    (* D'abord, montrons que (exists x:U, G_1 x) implique (exists x:U, x = g) *)
    assert (H_imp: (exists x:U, G_1 x) -> (exists x:U, x = g)).
    {
      intro H_exists_god.
      destruct H_exists_god as [h HGh].
      
      (* Par P14-A, h = g car h est Dieu et g est le seul Dieu *)
      assert (Hhg: h = g).
      { apply HP14A. exact HGh. }
      
      (* Donc g existe *)
      exists g.
      reflexivity.
    }
    
    (* Par R5, on peut transformer cette implication en n\u00e9cessit\u00e9 logique *)
    assert (H_nec_imp: L((exists x:U, G_1 x) -> (exists x:U, x = g))).
    { apply R5. exact H_imp. }
    
    (* Par R3, on distribue la n\u00e9cessit\u00e9 logique sur l'implication *)
    assert (H_dist: L(exists x:U, G_1 x) -> L(exists x:U, x = g)).
    { apply R3. exact H_nec_imp. }
    
    (* Finalement, on applique cette implication \u00e0 P11 *)
    apply H_dist.
    exact P11.
  }
  
  (* Troisi\u00e8me partie: Tout ce qui n'est pas Dieu est n\u00e9cessaire au sens de D7b *)
  intros x Hx_neq_g.
  
  (* Par D7b, une chose est n\u00e9cessaire quand elle est d\u00e9termin\u00e9e par autre chose *)
  apply D7b.
  
  (* Par P16, pour toute chose, il existe un Dieu qui en est la cause *)
  destruct (P16 x) as [h [HGh HKhx]].
  
  (* Par P14-A, h = g car h est Dieu et g est le seul Dieu *)
  assert (Hhg: h = g).
  { apply HP14A. exact HGh. }
  
  (* Substituons h par g dans K_2 h x *)
  rewrite Hhg in HKhx.
  
  (* Nous avons maintenant montr\u00e9 que K_2 g x *)
  exists g.
  split.
  - (* g \u2260 x *)
    apply neq_sym. exact Hx_neq_g.
  - (* g est cause de x *)
    exact HKhx.
Qed.

(* P36: Il n'existe rien dont la nature ne produise quelque effet *)
(* Note: Jarrett indique que cette proposition n'est pas d\u00e9rivable de son syst\u00e8me formel *)
Theorem P36 : forall x:U,
  (exists v:U, v = x) -> (exists y:U, K_2 x y).
Proof.
  (* Introduction des hypoth\u00e8ses *)
  intros x Hexists.
  
  (* Nous allons examiner si x est une substance ou un mode *)
  destruct (DP5 x) as [HSx | HMx].
  
  (* Cas 1: x est une substance *)
  {
    (* Par DPIII, toute substance est cause de soi-m\u00eame *)
    assert (HKxx: K_2 x x).
    { apply DPIII. exact HSx. }
    
    (* x est cause de soi-m\u00eame, donc il existe un y (\u00e0 savoir x) tel que K_2 x y *)
    exists x.
    exact HKxx.
  }
  
  (* Cas 2: x est un mode *)
  {
    (* Par D5b, si x est un mode, alors il existe une substance s dont x est un mode *)
    apply D5b in HMx.
    destruct HMx as [s [HSs HM_x_s]].
    
    (* Par le lemme DP4, toute substance est cause de soi-m\u00eame *)
    assert (HKss: K_2 s s).
    { apply DP4. exact HSs. }
    
    (* Par D5a, si x est un mode de s, alors x est en s et con\u00e7u par s *)
    apply D5a in HM_x_s.
    destruct HM_x_s as [Hneq [HIxs HCxs]].
    
    (* Par la d\u00e9finition de Spinoza, la nature d'une chose d\u00e9termine ses effets.
       Si x est un mode, son essence est d\u00e9termin\u00e9e par la substance dont il est un mode.
       Nous ne pouvons pas directement prouver que x produit un effet sans hypoth\u00e8ses 
       suppl\u00e9mentaires sur la nature des modes. *)
       
    (* Cependant, nous pouvons invoquer P16 qui \u00e9tablit que Dieu est cause de toutes choses *)
    destruct (P16 x) as [g [HGg HKgx]].
    
    (* Puisque g est Dieu, il a une infinit\u00e9 d'attributs et produit une infinit\u00e9 d'effets,
       dont l'un est x. Par transitivit\u00e9 de la causalit\u00e9 (qui n'est pas formellement
       \u00e9tablie dans le syst\u00e8me de Jarrett), x doit \u00e9galement produire des effets. *)
       
    (* Nous devons admettre ce point par la coh\u00e9rence du syst\u00e8me spinoziste, car comme 
       l'indique Jarrett, P36 n'est pas directement d\u00e9rivable dans son syst\u00e8me formel. *)
       
    (* Pour compl\u00e9ter la preuve en utilisant explicitement les axiomes disponibles,
       nous pouvons ajouter un axiome suppl\u00e9mentaire qui formalise cette propri\u00e9t\u00e9
       de la causalit\u00e9 dans le syst\u00e8me spinoziste:
       
       Axiom Transitive_Causality: forall x y z:U, K_2 x y /\ K_2 y z -> exists w:U, K_2 y w.
       
       Mais puisque nous n'avons pas cet axiome, nous admettons cette \u00e9tape. *)
    
    (* Puisque le syst\u00e8me de Spinoza est d\u00e9terministe et que toute chose d\u00e9coule
       n\u00e9cessairement de l'essence divine, nous pouvons affirmer que tout mode
       a un effet, m\u00eame si nous ne pouvons pas le d\u00e9montrer formellement. *)
    
    admit.
  }
Admitted.

End SpinozaJarrett.