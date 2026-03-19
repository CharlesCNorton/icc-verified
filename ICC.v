(******************************************************************************)
(*                                                                            *)
(*                      ROME STATUTE OF THE ICC (1998)                        *)
(*                                                                            *)
(*     International Criminal Court jurisdiction: genocide, crimes against    *)
(*     humanity, war crimes, crime of aggression. Elements of crimes,         *)
(*     complementarity principle, and admissibility criteria.                 *)
(*                                                                            *)
(*     The most serious crimes of concern to the international community      *)
(*     as a whole must not go unpunished.                                     *)
(*     (Preamble, Rome Statute)                                               *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: CORE CRIMES — ARTICLE 5                                        *)
(******************************************************************************)

(* Article 5: The Court has jurisdiction over four categories of crime *)
Inductive CoreCrime : Type :=
  | Genocide              (* Article 6 *)
  | CrimeAgainstHumanity  (* Article 7 *)
  | WarCrime              (* Article 8 *)
  | CrimeOfAggression.    (* Article 8 bis *)

(******************************************************************************)
(* SECTION 2: GENOCIDE — ARTICLE 6                                           *)
(******************************************************************************)

(* Article 6: Genocide requires specific intent (dolus specialis) to destroy
   in whole or in part a national, ethnical, racial, or religious group. *)

Inductive ProtectedGroup : Type :=
  | NationalGroup
  | EthnicalGroup
  | RacialGroup
  | ReligiousGroup.

Inductive GenocideAct : Type :=
  | KillingMembers
  | CausingGrievousHarm
  | DestructiveConditions
  | PreventingBirths
  | ForciblyTransferringChildren.

Record GenocideElements : Type := mkGenocide {
  ge_act            : GenocideAct;
  ge_target_group   : ProtectedGroup;
  ge_specific_intent: bool;   (* intent to destroy the group in whole or part *)
}.

Definition genocide_established (e : GenocideElements) : bool :=
  ge_specific_intent e.

(* Without specific intent, it is not genocide under the Rome Statute *)
Theorem no_intent_no_genocide : forall e,
  ge_specific_intent e = false ->
  genocide_established e = false.
Proof.
  intros e H. unfold genocide_established. exact H.
Qed.

(******************************************************************************)
(* SECTION 3: CRIMES AGAINST HUMANITY — ARTICLE 7                           *)
(******************************************************************************)

(* Article 7(1): Crimes against humanity require a widespread or systematic
   attack directed against any civilian population with knowledge of the attack. *)

Inductive CAHAct : Type :=
  | Murder_CAH
  | Extermination
  | Enslavement_CAH
  | Deportation
  | Imprisonment
  | Torture_CAH
  | SexualViolence
  | Persecution
  | EnforcedDisappearance
  | Apartheid
  | OtherInhumaneActs.

Record CAHElements : Type := mkCAH {
  cah_act                : CAHAct;
  cah_widespread_or_sys  : bool;   (* widespread OR systematic *)
  cah_against_civilians  : bool;   (* directed against civilian population *)
  cah_knowledge_of_attack: bool;   (* perpetrator knew of the attack *)
}.

Definition cah_established (e : CAHElements) : bool :=
  cah_widespread_or_sys   e &&
  cah_against_civilians   e &&
  cah_knowledge_of_attack e.

Theorem cah_requires_policy : forall e,
  cah_widespread_or_sys e = false ->
  cah_established e = false.
Proof.
  intros e H. unfold cah_established. rewrite H. reflexivity.
Qed.

Theorem cah_requires_civilian_target : forall e,
  cah_against_civilians e = false ->
  cah_established e = false.
Proof.
  intros e H.
  unfold cah_established. rewrite H. rewrite andb_false_r. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 4: WAR CRIMES — ARTICLE 8                                         *)
(******************************************************************************)

(* Article 8(1): The Court has jurisdiction over war crimes in particular
   when committed as part of a plan or policy or large-scale commission. *)

Inductive ConflictType : Type :=
  | InternationalArmedConflict
  | NonInternationalArmedConflict.

Inductive WarCrimeAct : Type :=
  | WillfulKilling
  | Torture_WC
  | UnlawfulConfinement
  | AttackingCivilians
  | UseForbiddenWeapons
  | ChildSoldiers
  | SexualViolence_WC
  | PillageProperty
  | StarvationOfCivilians.

Record WarCrimeElements : Type := mkWarCrime {
  wc_act            : WarCrimeAct;
  wc_conflict_type  : ConflictType;
  wc_nexus_to_conflict : bool;   (* act committed in context of armed conflict *)
  wc_protected_person  : bool;   (* victim is protected person or object *)
}.

Definition war_crime_established (e : WarCrimeElements) : bool :=
  wc_nexus_to_conflict e &&
  wc_protected_person  e.

Theorem war_crime_requires_nexus : forall e,
  wc_nexus_to_conflict e = false ->
  war_crime_established e = false.
Proof.
  intros e H. unfold war_crime_established. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 5: JURISDICTION — ARTICLES 12-13                                  *)
(******************************************************************************)

(* Article 12: The Court may exercise jurisdiction when:
   (a) the state on whose territory the crime occurred is a party, OR
   (b) the state of which the accused is a national is a party.
   Additionally, the UNSC may refer situations of non-party states. *)

Record JurisdictionBasis : Type := mkJurisdiction {
  jb_territorial_state_party : bool;  (* territorial state is a party *)
  jb_national_state_party    : bool;  (* accused's nationality state is a party *)
  jb_unsc_referral           : bool;  (* UN Security Council referral *)
  jb_state_consent           : bool;  (* non-party state consents *)
}.

Definition court_has_jurisdiction (j : JurisdictionBasis) : bool :=
  jb_territorial_state_party j ||
  jb_national_state_party    j ||
  jb_unsc_referral           j ||
  jb_state_consent           j.

Theorem unsc_referral_confers_jurisdiction : forall j,
  jb_unsc_referral j = true ->
  court_has_jurisdiction j = true.
Proof.
  intros j H.
  unfold court_has_jurisdiction. rewrite H.
  repeat rewrite orb_true_r. reflexivity.
Qed.

Theorem no_jurisdiction_without_basis : forall j,
  court_has_jurisdiction j = false ->
  jb_territorial_state_party j = false /\
  jb_national_state_party j = false /\
  jb_unsc_referral j = false /\
  jb_state_consent j = false.
Proof.
  intros j H.
  unfold court_has_jurisdiction in H.
  repeat rewrite orb_false_iff in H. tauto.
Qed.

(******************************************************************************)
(* SECTION 6: COMPLEMENTARITY — ARTICLE 17                                   *)
(******************************************************************************)

(* Article 17: A case is inadmissible if a state is genuinely willing and
   able to investigate or prosecute, UNLESS the state is unwilling or unable. *)

Inductive InvestigationState : Type :=
  | NotInvestigating        (* no national proceedings *)
  | InvestigatingGenuinely  (* genuine national proceedings ongoing *)
  | ShieldingFromJustice    (* proceedings designed to protect accused *)
  | CollapsedSystem.        (* judicial system unavailable *)

Definition complementarity_bars (s : InvestigationState) : bool :=
  match s with
  | InvestigatingGenuinely => true   (* admissibility barred *)
  | _                      => false  (* court may proceed *)
  end.

Theorem genuine_investigation_bars_admissibility :
  complementarity_bars InvestigatingGenuinely = true.
Proof. reflexivity. Qed.

Theorem shielding_does_not_bar :
  complementarity_bars ShieldingFromJustice = false.
Proof. reflexivity. Qed.

Theorem collapsed_system_does_not_bar :
  complementarity_bars CollapsedSystem = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 7: ADMISSIBILITY — ARTICLE 17(1)                                  *)
(******************************************************************************)

Record AdmissibilityCheck : Type := mkAdmiss {
  ad_complementarity_bars  : bool;  (* true = national proceedings bar the case *)
  ad_gravity_sufficient    : bool;  (* sufficient gravity — Art. 17(1)(d) *)
  ad_ne_bis_in_idem        : bool;  (* true = person already tried — Art. 20 *)
}.

(* A case is admissible when: not barred by complementarity, sufficient gravity,
   and no ne bis in idem bar *)
Definition case_admissible (a : AdmissibilityCheck) : bool :=
  negb (ad_complementarity_bars a) &&
  ad_gravity_sufficient a &&
  negb (ad_ne_bis_in_idem a).

Theorem low_gravity_inadmissible : forall a,
  ad_gravity_sufficient a = false ->
  case_admissible a = false.
Proof.
  intros a H.
  unfold case_admissible. rewrite H. rewrite andb_false_r. reflexivity.
Qed.

Theorem ne_bis_bars_case : forall a,
  ad_ne_bis_in_idem a = true ->
  case_admissible a = false.
Proof.
  intros a H.
  unfold case_admissible. rewrite H. simpl.
  repeat rewrite andb_false_r. reflexivity.
Qed.

Theorem complementarity_bars_case : forall a,
  ad_complementarity_bars a = true ->
  case_admissible a = false.
Proof.
  intros a H.
  unfold case_admissible. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 8: INDIVIDUAL CRIMINAL RESPONSIBILITY — ARTICLE 25                *)
(******************************************************************************)

(* Article 25: A person is criminally responsible if they:
   (a) commit a crime individually, jointly, or through another;
   (b) order, solicit, or induce a crime;
   (c) aid, abet, or otherwise assist;
   (d) contribute to a group crime. *)

Inductive ModeOfLiability : Type :=
  | PrincipalPerp           (* 25(3)(a) — individual or co-perpetration *)
  | IndirectPerp            (* 25(3)(a) — through another person *)
  | Order_SolicitInduce     (* 25(3)(b) *)
  | AidAbetAssist           (* 25(3)(c) *)
  | GroupContribution.      (* 25(3)(d) *)

(* Article 27: Official capacity is irrelevant — heads of state are not immune *)
Definition official_capacity_irrelevant : bool := true.

Lemma immunity_does_not_apply :
  official_capacity_irrelevant = true.
Proof. reflexivity. Qed.

(* Article 26: Persons under 18 at time of offence not subject to jurisdiction *)
Definition age_at_offence_18 (age : nat) : bool :=
  Nat.leb 18 age.

Theorem minor_excluded : forall age,
  age < 18 ->
  age_at_offence_18 age = false.
Proof.
  intros age H.
  unfold age_at_offence_18.
  apply Nat.leb_nle. lia.
Qed.

(******************************************************************************)
(* SECTION 9: PENALTIES — ARTICLE 77                                         *)
(******************************************************************************)

(* Article 77: The Court may impose:
   - Imprisonment up to 30 years; or
   - Life imprisonment for extreme gravity.
   No death penalty. *)

Definition max_determinate_sentence : nat := 30.  (* years *)

Inductive Sentence : Type :=
  | TermImprisonment (years : nat)
  | LifeImprisonment
  | Acquittal.

Definition sentence_within_statute (s : Sentence) : bool :=
  match s with
  | Acquittal              => true
  | LifeImprisonment       => true
  | TermImprisonment years => Nat.leb years max_determinate_sentence
  end.

Lemma thirty_year_sentence_valid :
  sentence_within_statute (TermImprisonment 30) = true.
Proof. reflexivity. Qed.

Lemma thirty_one_year_sentence_invalid :
  sentence_within_statute (TermImprisonment 31) = false.
Proof. reflexivity. Qed.

Lemma life_sentence_valid :
  sentence_within_statute LifeImprisonment = true.
Proof. reflexivity. Qed.

(* The Rome Statute does not permit the death penalty *)
Inductive StatutoryPenalty : Type :=
  | Stat_Imprisonment
  | Stat_LifeImprisonment
  | Stat_DeathPenalty.

Definition penalty_permitted (p : StatutoryPenalty) : bool :=
  match p with
  | Stat_DeathPenalty => false
  | _                 => true
  end.

Theorem death_penalty_not_permitted :
  penalty_permitted Stat_DeathPenalty = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 10: SUMMARY                                                        *)
(******************************************************************************)

(*
  This file formalizes the Rome Statute of the International Criminal Court (1998).

  Structure:
    1. Core crimes (Art. 5): Genocide, Crimes Against Humanity, War Crimes,
       Crime of Aggression.
    2. Genocide (Art. 6): specific intent (dolus specialis) required to destroy
       a protected group.
    3. Crimes against humanity (Art. 7): widespread or systematic attack on
       civilians; perpetrator's knowledge required.
    4. War crimes (Art. 8): nexus to armed conflict; protected persons.
    5. Jurisdiction (Arts. 12-13): territorial state, nationality state, UNSC
       referral, or state consent — any one suffices.
    6. Complementarity (Art. 17): genuine national proceedings bar admissibility;
       shielding and collapsed systems do not.
    7. Admissibility: no complementarity bar + sufficient gravity + no ne bis in idem.
    8. Individual responsibility (Art. 25): five modes of liability;
       official capacity irrelevant (Art. 27); minors excluded (Art. 26).
    9. Penalties (Art. 77): up to 30 years or life imprisonment; no death penalty.

  Key theorems:
    - no_intent_no_genocide
    - cah_requires_policy / cah_requires_civilian_target
    - war_crime_requires_nexus
    - unsc_referral_confers_jurisdiction
    - genuine_investigation_bars_admissibility / shielding_does_not_bar
    - low_gravity_inadmissible / ne_bis_bars_case / complementarity_bars_case
    - death_penalty_not_permitted
    - minor_excluded (age < 18 outside jurisdiction)

  All proofs closed; no Admitted lemmas.
*)
