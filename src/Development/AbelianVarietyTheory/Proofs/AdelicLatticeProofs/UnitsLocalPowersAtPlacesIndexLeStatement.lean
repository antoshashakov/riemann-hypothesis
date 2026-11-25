module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.unitsLocalPowersAtPlaces_index_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p → (finPow p F S).index ≠ 0 ∧ (finPow p F S).index ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  first | exact @GlobalTheory.CNorm.index_finPow_le | exact GlobalTheory.CNorm.index_finPow_le | (intros; apply GlobalTheory.CNorm.index_finPow_le <;> assumption)
