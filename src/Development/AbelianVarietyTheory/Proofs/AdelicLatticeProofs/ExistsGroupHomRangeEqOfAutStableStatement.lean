module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_group_hom_range_eq_of_isPre : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  first | exact @GlobalTheory.ClassFin.IsPre.exists_group_range | exact GlobalTheory.ClassFin.IsPre.exists_group_range | (intros; apply GlobalTheory.ClassFin.IsPre.exists_group_range <;> assumption)
