module

public import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion
public import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
public import Statements

@[expose] public section

/-!
Source interfaces for the Alpöge proof, arranged alongside Adriazola's reconstruction.
These declarations reuse the checked archive. They do not identify independently
defined manuscript objects with source objects or claim any mathematical shortening.
-/

namespace Principia.Adriazola

/-- J1: exact source interface. -/
def windowCriterion :=
  @Deduction.zeroFree_of_rpow_window

/-- J2b: exact source interface. -/
def excessIdentity :=
  @Deduction.ch_balance

/-- J3: exact source interface. -/
def characterHosts :=
  @UpperTheory.Top.supplyChi

/-- J4: exact source interface. -/
def cohomologyWindows :=
  @UpperTheory.One.vwin_of_row

/-- J4a: exact source interface. -/
def uniformCohomology :=
  @UpperTheory.V.ZK.lemmaK_litN_alt

/-- J4b: exact source interface. -/
def twistedDivisibility :=
  @UpperTheory.Top.divinN_of_hypV

/-- J5: exact source interface. -/
def thetaInputs :=
  @UpperTheory.LiteratureTheorems.published_results_first

/-- J5a: exact source interface. -/
def chainGain :=
  @GlobalTheory.Top.closed_linkG_of_duty

/-- J6: exact source interface. -/
def heckeGaloisInputs :=
  @UpperTheory.LiteratureTheorems.published_results_eigen

/-- J6a: exact source interface. -/
def slopeLoss :=
  @Formalism.MainNotions.J.lemma_five_one_of_theorem_two

/-- J7: exact source interface. -/
def thetaMatching :=
  @UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature

/-- J7a: exact source interface. -/
def periodRationality :=
  @Formalism.L2.DIV.RatFullPt.buRational_of

/-- J7b: exact source interface. -/
def rowScalars :=
  @Formalism.IndefR.Cx.CxData.scal_rowsR

/-- J7c: exact source interface. -/
def liftScalars :=
  @Formalism.IndefR.Cx.CxData.scal_liftsR

/-- J9a: exact source interface. -/
def commonFamilySelection :=
  @UpperTheory.Top.topDesWin

/-- J10: exact source interface. -/
def theoremAAccounting :=
  @Deduction.ch_top

/-- J11a: exact source interface. -/
def familyPrimeBound :=
  @UpperTheory.Comparison₂.level_gm_le_on_family_scales

/-- J11: exact source interface. -/
def nonvanishingFromConstruction :=
  @UpperTheory.Top.every_character_of_green_v_win

/-- The existing Galois-row theorem supplies the literature input record. -/
theorem literatureInputs : UpperTheory.LiteratureTheorems.OpenLiteratureStatements := by
  have h := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  exact
    { caraianiLocalGlobalDual := h
      localLanglandsExists := UpperTheory.Zero.LLC.recTExists
      galoisRepOfPolarizedPairLit := h }

/-- The covolume theorem with all its existing published-input proofs supplied. -/
theorem covolumeBound (O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements) :
    GlobalTheory.CovTop.CovolumeBoundOfX := by
  exact SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    (UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O)
    (UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O)
    (UpperTheory.LiteratureTheorems.poincare_lelong_inv_of_literature O)
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
    (UpperTheory.LiteratureTheorems.fargues_exact_of_literature O)
    (UpperTheory.LiteratureTheorems.zarhin_statement O)
    (UpperTheory.LiteratureTheorems.nef_rr_of_literature O)
    (UpperTheory.LiteratureTheorems.siegel_toroidal_integral_of_literature O)
    (UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O)
    (UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O)
    (UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O)
    (UpperTheory.LiteratureTheorems.ar_degree_of_literature O)
    (UpperTheory.LiteratureTheorems.published_results_arithmetic O)
    (UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O)

/-- A single compatible source construction, with the linked local bound supplied. -/
theorem compatibleConstruction
    (P : GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses)
    (F : GlobalTheory.FunPr.ThetaLocalInputs)
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : GlobalTheory.CovTop.CovolumeBoundOfX)
    (hL : UpperTheory.Zero.LLC.RecTExists) :
    Nonempty (GlobalTheory.Fc.HypsAlt GlobalTheory.Fc.S0.NL
      GlobalTheory.Fc.DefiniteSideCondition) := by
  exact UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F hA hM hX hL fun cDep =>
      UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
        (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep)

/-- All five official conclusion types, conditional only on all-character nonvanishing. -/
theorem officialConclusions (h : UpperTheory.EveryCharacter) :
    RiemannHypothesis ∧ RiemannZetaZerosOnLine ∧
    DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
    PrimitiveDirichletLZerosOnLine := by
  refine ⟨Claim.zeta h, Claim.zeta h, h, Claim.strip h, ?_⟩
  intro N _ χ _ s h₀ h₁ hz
  exact Claim.strip h N χ s h₀ h₁ hz

/-- Recomposition of the existing source proof; no independent manuscript claim. -/
theorem allFive :
    RiemannHypothesis ∧ RiemannZetaZerosOnLine ∧
    DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
    PrimitiveDirichletLZerosOnLine := by
  let O := literatureInputs
  let P := heckeGaloisInputs O
  let F := thetaInputs O
  obtain ⟨hA, hM⟩ := thetaMatching O
  have hV := cohomologyWindows O.caraianiLocalGlobalDual
  have hH := compatibleConstruction P F hA hM (covolumeBound O) O.localLanglandsExists
  have hG := GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters
  exact officialConclusions (nonvanishingFromConstruction hG hV hH)

end Principia.Adriazola


open scoped BigOperators
namespace Principia.Adriazola

/-- The seven scalar inequalities of the reconstruction, before expanding logarithms.
Here g includes the factor m, P is the unmixed period main term, and B is
the sum of the logarithmic node terms over the m lifts. -/
theorem accountingCore {W : Type} [Fintype W] [Nonempty W]
    (d μN μM h E logT : W → ℝ) (hd : ∀ u, 0 < d u)
    (S Γ L μC P A B g e1 e2 e3 e4 e5 e6 e7 : ℝ) (hA : 0 ≤ A)
    (A1 : S ≤ Γ + e1)
    (A2 : ∀ u, μM u + Γ + L - E u - e2 ≤ μN u)
    (A3 : (∑ u, d u * (μN u - h u)) / (∑ u, d u) - e3 ≤ μC)
    (A4 : ∀ u, μC + h u - L ≤ P - A * logT u + e4)
    (A5 : ∀ u, E u ≤ A * g + e5)
    (A6 : ∀ u, B + g - e6 ≤ logT u)
    (A7 : ∀ u, -e7 ≤ μM u) :
    S - P + A * B ≤ e1 + e2 + e3 + e4 + e5 + A * e6 + e7 := by
  classical
  have hden : 0 < ∑ u, d u :=
    Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  have hmean : (∑ u, d u * (μN u - h u)) / (∑ u, d u) ≤ μC + e3 := by
    linarith only [A3]
  have hprod := (div_le_iff₀ hden).mp hmean
  have hsum : (∑ u, d u * (μN u - h u)) ≤
      ∑ u, d u * (μC + e3) := by
    rw [← Finset.sum_mul]
    nlinarith only [hprod]
  obtain ⟨u, _, hu⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  have hpoint : μN u - h u ≤ μC + e3 := by
    nlinarith only [hu, hd u]
  have hlog : -(A * logT u) ≤ -(A * (B + g - e6)) :=
    neg_le_neg (mul_le_mul_of_nonneg_left (A6 u) hA)
  nlinarith only [A1, A2 u, A4 u, A5 u, A7 u, hpoint, hlog]


/-- Proposition 3's scalar accounting with its logarithmic main term expanded. -/
theorem sevenInequalityAccounting
    {W : Type} [Fintype W] [Nonempty W] (m f nT : ℕ) (hf : 0 < f)
    (a : Fin nT → ℝ) (ha : ∀ t, 0 < a t)
    (w : Fin m → Fin f → ℝ) (hw : ∀ j ρ, 0 < w j ρ)
    (v : ℝ) (hv : 0 < v) (γ lam g : ℝ)
    (d μN μM h E logT : W → ℝ) (hd : ∀ u, 0 < d u)
    (S Γ L μC e1 e2 e3 e4 e5 e6 e7 : ℝ)
    (A1 : S ≤ Γ + e1)
    (A2 : ∀ u, μM u + Γ + L - E u - e2 ≤ μN u)
    (A3 : (∑ u, d u * (μN u - h u)) / (∑ u, d u) - e3 ≤ μC)
    (A4 : ∀ u, μC + h u - L ≤
      ∑ t, ((m : ℝ) * (a t * Real.log (a t) - a t) -
        (m : ℝ) * a t * (γ + Real.log (Real.pi / v) - lam) -
        a t * logT u) + e4)
    (A5 : ∀ u, E u ≤ (m : ℝ) * (∑ t, a t) * g + e5)
    (A6 : ∀ u, (∑ j, (1 / (f : ℝ)) *
      ∑ ρ, Real.log (w j ρ * v / Real.pi)) + (m : ℝ) * g - e6 ≤ logT u)
    (A7 : ∀ u, -e7 ≤ μM u) :
    S ≤ (∑ j, ∑ t, a t * (Real.log (a t) - 1 - γ + lam -
      (1 / (f : ℝ)) * ∑ ρ, Real.log (w j ρ))) +
      e1 + e2 + e3 + e4 + e5 + (∑ t, a t) * e6 + e7 := by
  classical
  let A := ∑ t, a t
  let logΩ := γ + Real.log (Real.pi / v) - lam
  let p0 := ∑ t, a t * (Real.log (a t) - 1 - logΩ)
  let node := fun j : Fin m => (1 / (f : ℝ)) *
    ∑ ρ, Real.log (w j ρ * v / Real.pi)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun t _ => (ha t).le)
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hnode (j : Fin m) : node j =
      (1 / (f : ℝ)) * (∑ ρ, Real.log (w j ρ)) +
        Real.log (v / Real.pi) := by
    have hlog (ρ : Fin f) : Real.log (w j ρ * v / Real.pi) =
        Real.log (w j ρ) + Real.log (v / Real.pi) := by
      rw [mul_div_assoc, Real.log_mul (hw j ρ).ne'
        (div_pos hv Real.pi_pos).ne']
    dsimp [node]
    simp_rw [hlog, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  have hA4 : ∀ u, μC + h u - L ≤
      (m : ℝ) * p0 - A * logT u + e4 := by
    intro u
    have heq :
        (∑ t, ((m : ℝ) * (a t * Real.log (a t) - a t) -
          (m : ℝ) * a t * logΩ - a t * logT u)) =
        (m : ℝ) * p0 - A * logT u := by
      calc
        _ = ∑ t, ((m : ℝ) * (a t * (Real.log (a t) - 1 - logΩ)) -
            a t * logT u) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          dsimp [p0, A]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have hbound := A4 u
    change μC + h u - L ≤
      (∑ t, ((m : ℝ) * (a t * Real.log (a t) - a t) -
        (m : ℝ) * a t * logΩ - a t * logT u)) + e4 at hbound
    simpa only [heq] using hbound
  have hA5 : ∀ u, E u ≤ A * ((m : ℝ) * g) + e5 := by
    intro u
    dsimp [A]
    nlinarith only [A5 u]
  have hcore := accountingCore d μN μM h E logT hd
    S Γ L μC ((m : ℝ) * p0) A (∑ j, node j) ((m : ℝ) * g)
    e1 e2 e3 e4 e5 e6 e7 hA A1 A2 A3 hA4 hA5 A6 A7
  have hmain :
      (∑ j, ∑ t, a t * (Real.log (a t) - 1 - γ + lam -
        (1 / (f : ℝ)) * ∑ ρ, Real.log (w j ρ))) =
      (m : ℝ) * p0 - A * (∑ j, node j) := by
    calc
      _ = ∑ j, ∑ t, (a t * (Real.log (a t) - 1 - logΩ) -
          a t * node j) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro t _
        rw [hnode]
        dsimp [logΩ]
        rw [Real.log_div Real.pi_ne_zero hv.ne',
          Real.log_div hv.ne' Real.pi_ne_zero]
        ring
      _ = _ := by
        dsimp [p0, A]
        simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
  rw [hmain]
  dsimp [A] at hcore
  nlinarith only [hcore]

end Principia.Adriazola

#check Principia.Adriazola.windowCriterion
#check Principia.Adriazola.excessIdentity
#check Principia.Adriazola.characterHosts
#check Principia.Adriazola.cohomologyWindows
#check Principia.Adriazola.uniformCohomology
#check Principia.Adriazola.twistedDivisibility
#check Principia.Adriazola.thetaInputs
#check Principia.Adriazola.chainGain
#check Principia.Adriazola.heckeGaloisInputs
#check Principia.Adriazola.slopeLoss
#check Principia.Adriazola.thetaMatching
#check Principia.Adriazola.periodRationality
#check Principia.Adriazola.rowScalars
#check Principia.Adriazola.liftScalars
#check Principia.Adriazola.commonFamilySelection
#check Principia.Adriazola.theoremAAccounting
#check Principia.Adriazola.familyPrimeBound
#check Principia.Adriazola.nonvanishingFromConstruction
#check Principia.Adriazola.literatureInputs
#check Principia.Adriazola.covolumeBound
#check Principia.Adriazola.compatibleConstruction
#check Principia.Adriazola.officialConclusions
#check Principia.Adriazola.allFive
#check Principia.Adriazola.accountingCore
#check Principia.Adriazola.sevenInequalityAccounting
#print axioms Principia.Adriazola.windowCriterion
#print axioms Principia.Adriazola.excessIdentity
#print axioms Principia.Adriazola.characterHosts
#print axioms Principia.Adriazola.cohomologyWindows
#print axioms Principia.Adriazola.uniformCohomology
#print axioms Principia.Adriazola.twistedDivisibility
#print axioms Principia.Adriazola.thetaInputs
#print axioms Principia.Adriazola.chainGain
#print axioms Principia.Adriazola.heckeGaloisInputs
#print axioms Principia.Adriazola.slopeLoss
#print axioms Principia.Adriazola.thetaMatching
#print axioms Principia.Adriazola.periodRationality
#print axioms Principia.Adriazola.rowScalars
#print axioms Principia.Adriazola.liftScalars
#print axioms Principia.Adriazola.commonFamilySelection
#print axioms Principia.Adriazola.theoremAAccounting
#print axioms Principia.Adriazola.familyPrimeBound
#print axioms Principia.Adriazola.nonvanishingFromConstruction
#print axioms Principia.Adriazola.literatureInputs
#print axioms Principia.Adriazola.covolumeBound
#print axioms Principia.Adriazola.compatibleConstruction
#print axioms Principia.Adriazola.officialConclusions
#print axioms Principia.Adriazola.allFive
#print axioms Principia.Adriazola.accountingCore
#print axioms Principia.Adriazola.sevenInequalityAccounting
