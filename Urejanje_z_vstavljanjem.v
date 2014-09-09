(** UREJANJE Z VSTAVLJANJEM RES DELUJE!!!
Projekt Barbare Bajcer in Jane Vidrih. :) **)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sorting.


(** Vstavi element x pred prvi večji element v seznamu l. **)
Function vstavi (x : Z) (l : list Z) :=
  match l with
   | nil => x :: nil
   | y :: l' => 
     if Z.leb x y then (x :: y :: l') else y :: vstavi x l'
  end.


(** Funkcija nam uredi seznam po algoritmu urejanja z vstavljanjem. **)
Function insertion (l :list Z) := 
  match l with
    | nil => nil
    | x :: l' => 
        let l'' := insertion l' in vstavi x l''
  end.

(** Eval compute in (insertion(2::3::1::15::3999::8::146::nil)%Z). **)


Lemma brez_prvega (l : list Z) : forall a : Z, urejen (a :: l) -> urejen (l).
Proof.
  induction l ; firstorder.
Qed.


Lemma brez_drugega (a b : Z) (l : list Z) : urejen (a :: b :: l) -> urejen (a :: l).
Proof.
  induction l ; firstorder.
Qed.


(** Če vemo, da je x manjši od prvega elementa v seznamu, vstavimo x na začetek.**)
Lemma vstavi_zacetek (x y : Z) (l : list Z) :
(x <= y)%Z -> vstavi x (y :: l) = x :: y :: l.
Proof.
  intro.
  simpl.
  apply Zle_is_le_bool in H.
  now rewrite H.
Qed.


Lemma vstavi_vecjega (a x : Z)(l : list Z):
 (a < x)%Z -> vstavi x (a ::l) = a ::(vstavi x l).
Proof.
  intro.
  simpl.
  apply Z.leb_gt in H.
  now rewrite H. 
Qed.


(** Če element y pripada seznamu, ki smo mu dodali x, potem je ali y enak x ali y pripada prvotnemu seznamu. **)
Lemma element_vstavi (x y : Z) (l : list Z) : In y (vstavi x l) -> In y l \/ (y = x)%Z.
Proof.
  intro.
  induction l.
  - simpl in H.
    firstorder.
  - case_eq (x <=? a)%Z.
    + intro.
      rewrite vstavi_zacetek in H.
      *firstorder.
      *apply Zle_is_le_bool in H0.
       assumption.
    + intro.
      apply Z.leb_gt in H0.
      rewrite vstavi_vecjega in H.
      * firstorder.
      * assumption.      
Qed.


(** V urejenem seznamu so vsi večji od prvega elementa. **)
Lemma prvi_najmanjsi (a : Z) (l : list Z) : urejen (a :: l) -> forall y, In y l -> (a <= y)%Z.
Proof.
  induction l.
  - firstorder.
  - intros.
    assert (urejen (a :: a0 :: l)) as G.
    assumption.
    apply brez_drugega in H.
    firstorder.
Qed.


(** Če vstavljamo element s funkcijo 'vstavi' v urejen seznam, dobimo urejen seznam. **)
Lemma vstavi_deluje (x : Z) (l : list Z) : urejen l -> urejen ( vstavi x l).
Proof.
   induction l ; auto.
   intro.
   simpl.
   case_eq ((x <=? a)%Z).
   - intro.
     firstorder.
     now apply Zle_bool_imp_le.
   - intros.
     assert (urejen(a::l)) as G.
     assumption.
     apply brez_prvega in H.
     assert (urejen(l)) as M.
     assumption.
     apply IHl in H.
     assert (p := (prvi_najmanjsi a l G)).
     apply Z.leb_gt in H0.
     apply urejen_lt_cons.
     + intros.
       apply element_vstavi in H1.
       destruct H1 ; firstorder.
     + assumption.
Qed.


(** Funkcija insertion vrne urejen seznam. **)
Theorem algoritem_insertion_ureja (l: list Z):
urejen (insertion l).
Proof.
  apply (list_ind_2 (fun l => urejen (insertion l))) ; simpl ; auto.
  intros.
  apply vstavi_deluje.
  apply vstavi_deluje.
  assumption.
Qed.


(** Drugi del dokaza: Algoritem insertion vrne permutacijo prvotnega seznama **)
 

(**Če vstavimo v seznam element x, ki se v seznamu že pojavi, se število pojavitev x poveča za ena **)
Lemma vstavi_enakega (x : Z)(l: list Z): pojavi x (vstavi x l) = S(pojavi x l).
Proof.
  induction l.
  - simpl.
    rewrite Z.eqb_refl ; auto.
  - simpl.
    case_eq (x <=? a)%Z.
    + intro.
      apply Zle_is_le_bool in H.
      case_eq (x =? a)%Z.
      * intro.
        apply Z.eqb_eq in H0.
        rewrite <- H0.
        simpl.
        rewrite Z.eqb_refl ; auto.
      * intro ; simpl.
        rewrite Z.eqb_refl.
        rewrite H0 ; auto.
    + intro ; simpl.
      case_eq (x =? a)%Z.
      apply Z.leb_gt in H.
      apply Z.lt_neq in H.
      apply Z.eqb_neq in H.
      firstorder.
      firstorder.     
Qed.
      

(** Če vstavimo v seznam element y != x, potem se število pojavitev x ne spremeni. **)
Lemma vstavi_drugacnega (x y : Z)(l : list Z) : 
((x =? y)%Z = false) -> pojavi x (vstavi y l) = pojavi x l.
Proof.
  intro.
  induction l.
  - simpl.
    rewrite H ; auto.
  - simpl.
    case_eq (x =? a)%Z.
    + intro G.
      apply Z.eqb_eq in G.
      case_eq ( y <=? a)%Z.
      * intro.
        rewrite <- G.
        simpl.
        rewrite H.
        rewrite Z.eqb_refl ; auto.
      * intro.
        rewrite <- G.
        simpl.
        rewrite IHl.
        rewrite Z.eqb_refl ; auto.
    + intro.
      case_eq (y <=? a)%Z.
      * intro ; simpl.
        rewrite H.
        rewrite H0 ; auto.
      * intro ; simpl.
        rewrite H0.
        firstorder.
Qed.  
        

(** Algoritem insertion vrne permutacijo zacetnega seznama. **)
Theorem insertion_je_permutacija (l : list Z): 
permutiran l (insertion l).
Proof.
  intro.
  induction l.
  firstorder.
  - simpl.
    case_eq (x =? a)%Z.
    + intro.
      apply Z.eqb_eq in H.
      rewrite <- H.
      rewrite IHl.
      rewrite (vstavi_enakega x (insertion l)) ; auto.
    + intro.
      rewrite (vstavi_drugacnega x a(insertion l)).
      firstorder.
      assumption.
Qed.
    
(** Lep pozdrav,
 Barbara in Jana :) **)