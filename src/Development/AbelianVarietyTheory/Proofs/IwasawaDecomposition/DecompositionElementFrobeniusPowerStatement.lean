module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPower
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne


theorem _root_.GlobalTheory.T.decomposition_element_frobenius_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω, g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x → A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_normV_resPow | exact GlobalTheory.WeilDeligne.exists_pow_normV_resPow | (intros; apply GlobalTheory.WeilDeligne.exists_pow_normV_resPow <;> assumption)
