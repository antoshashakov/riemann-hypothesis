module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p → (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧ ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  first | exact @GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | exact GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | (intros; apply GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono <;> assumption)
