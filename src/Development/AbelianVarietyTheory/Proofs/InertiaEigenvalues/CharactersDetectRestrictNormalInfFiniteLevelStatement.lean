module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l)) (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ), (∀ i, x i ∈ Set.range (algebraMap L (Om l))) → (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) → (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') → Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  first | exact @GlobalTheory.PMon.Ram.detects_restrictNormal_inf | exact GlobalTheory.PMon.Ram.detects_restrictNormal_inf | (intros; apply GlobalTheory.PMon.Ram.detects_restrictNormal_inf <;> assumption)
