module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_vanishing_along_ideal_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A),
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  first | exact @GlobalTheory.CompanionTheory.TowerEnd.vanish | exact GlobalTheory.CompanionTheory.TowerEnd.vanish | (intros; apply GlobalTheory.CompanionTheory.TowerEnd.vanish <;> assumption)
