module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  first | exact @GlobalTheory.Cyc.phi_free | exact GlobalTheory.Cyc.phi_free | (intros; apply GlobalTheory.Cyc.phi_free <;> assumption)
