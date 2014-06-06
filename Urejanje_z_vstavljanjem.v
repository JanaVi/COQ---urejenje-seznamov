(** UREJANJE Z VSTAVLJANJEM 
Projekt Barbare Bajcer in Jane Vidrih.
Priporočava, da še ne bereš dalje :) *)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sorting.

SearchAbout (Z.leb).

Function vstavi (x : Z) (l : list Z) :=
  match l with
   | nil => x :: nil
   | y :: l' => 
     if Z.leb x y then (x :: y :: l') else y :: vstavi x l'
  end.


Function insertion (l :list Z) := 
  match l with
    | nil => nil
    | x :: l' => 
        let l'' := insertion l' in vstavi x l''
  end.

Eval compute in (insertion(2::3::1::15::3999::8::146::nil)%Z).


Lemma brez_prvega (l : list Z) : forall a : Z, urejen (a :: l) -> urejen (l).
Proof.
  induction l ; firstorder.
Qed.


Lemma brez_drugega (a b : Z) (l : list Z) : urejen (a :: b :: l) -> urejen (a :: l).
Proof.
  induction l ; firstorder.
Qed.


Lemma najmanjsi_na_zacetku (a : Z) (l : list Z) : urejen(l) -> (forall y, In y l -> (a<=y)%Z) -> urejen (a :: l).
Proof.
  intros.
  admit.
  (* destruct H.
  induction l ; firstorder. *)
Qed.


Lemma element_vstavi (x y : Z) (l : list Z) : In y (vstavi x l) -> In y l \/ (y = x)%Z.
Proof.
  intro.
  induction l.
  - simpl in H.
    firstorder.
  - admit.
Qed.


Lemma element (y x : Z) (l : list Z) : In y (x :: l) -> In y l \/ (y = x)%Z.
Proof.
  intro.
  induction l.
  - simpl in H.
    firstorder.
  - admit.
Qed.


Lemma prvi_najmanjsi (a : Z) (l : list Z) : urejen (a :: l) -> forall y, In y l -> (a <= y)%Z.
Proof.
  induction l.
  - firstorder.
  - intros.
    assert (urejen (a :: a0 :: l)) as G.
    assumption.
    apply brez_drugega in H.
    
    
    admit.
Qed.





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
     apply najmanjsi_na_zacetku.
     + assumption.
     + intros.
       apply element_vstavi in H1.
       destruct H1 ; firstorder.    
Qed.


Theorem AlgoritemDeluje (l: list Z):
urejen (insertion l).
Proof.
  apply (list_ind_2 (fun l => urejen (insertion l))) ; simpl ; auto.
  intros.
  apply vstavi_deluje.
  admit.
Qed.
  
 
