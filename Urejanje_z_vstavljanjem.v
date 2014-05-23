(** UREJANJE Z VSTAVLJANJEM 
Projekt Barbare Bajcer in Jane Vidrih.
Priporočava, da ne bereš dalje :) *)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.

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

Lemma vstavi_deluje (x : Z) (l : list Z) : urejen ( vstavi x l).
Proof.
  apply (list_ind_2 (fun l => urejen (vstavi x l))) ; simpl ; auto.
  - intros.
   destruct (x <=? x0)%Z as []eqn:? ; simpl ; intuition.
   + admit.
   + admit.
  -  admit. (** Vprašanje, če je to vredu, ali ta reč dejansko velja za vse a,b
     ali samo če b>a????:    
     intros ; simpl ; auto.
    destruct (x <=? a)%Z as []eqn:?.
    + simpl.
      intuition. *)
Qed.


Theorem AlgoritemDeluje (l: list Z):
urejen (insertion l).
Proof.
  apply (list_ind_2 (fun l => urejen (insertion l))) ; simpl ; auto.
  intros.
  apply vstavi_deluje.
Qed.
  
 
