# Projet Spinoza

Ce projet est une formalisation en Coq des propositions du Livre I de l'Éthique de Spinoza, selon la formalisation logique proposée par Charles Jarrett dans son article "The Logical Structure of Spinoza's Ethics, Part I" (1978).

Je compte continuer avec le livre II prochainement, mais il y a d'abord un travail de traduction logique à faire ! Ce qui implique des présupposés philosophiques. La formalisation s'appuie sur la logique modale, permettant de distinguer entre nécessité logique, nécessité naturelle et possibilité.

## CAVEAT

Ces démonstrations reposent sur une interprétation philosophique (puisque c'est une formalisation) de l'Ethique, et donc sont responsabilité partagée de Spinoza et de Charles Jarrett.

## Contenu du projet

Le fichier principal `De_Deo.v` contient :

- Les définitions formelles des opérateurs modaux (nécessité logique, possibilité, nécessité naturelle), qui sied à la philosophie de Spinoza
- Le lexique des prédicats unaires, binaires et ternaires correspondant aux concepts spinozistes
- Les axiomes modaux fondamentaux
- Les définitions de Spinoza (causa sui, substance, attribut, mode, Dieu, etc.)
- Les axiomes proposés par Spinoza et complétés par Jarrett
- Les démonstrations formelles des 36 propositions du Livre I (excepté la P33 et la P36 qui sont indérivable du système)

## Prérequis

Pour exécuter ce projet, vous aurez besoin de :

1. [Coq](https://coq.inria.fr/) (version 8.13 ou supérieure recommandée)
2. Un IDE compatible avec Coq comme CoqIDE ou [Proof General](https://proofgeneral.github.io/) pour Emacs

## Installation

1. Installez Coq en suivant les instructions sur le [site officiel](https://coq.inria.fr/download)
2. Clonez ce dépôt :
   ```
   git clone https://github.com/votre-nom/Projet-Spinoza.git
   cd Projet-Spinoza
   ```

## Exécution

### Avec CoqIDE

1. Ouvrez CoqIDE
2. Ouvrez le fichier `De_Deo.v`
3. Utilisez le bouton "Step forward" ou la combinaison de touches Ctrl+Right pour avancer pas à pas dans la preuve

### Avec Proof General (Emacs)

1. Ouvrez Emacs
2. Ouvrez le fichier `De_Deo.v`
3. Utilisez C-c C-n pour avancer d'une étape dans la preuve ou C-c C-Enter pour avancer jusqu'au curseur

### En ligne de commande

Pour compiler le projet sans interface graphique :

```
coqc De_Deo.v
```

## Remerciements

- Charles Jarrett pour sa formalisation logique de l'Éthique
- L'équipe de développement de Coq pour cet assistant de preuve
- Claude 3.5, le LLM qui m'a beaucoup aidé à réaliser ce projet, parfois étonnamment fort en démonstrations.