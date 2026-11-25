module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpen
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.compact_meets_finitely_many_leftCosets_open : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (K : Set G), IsOpen (U : Set G) → IsCompact K → ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  first | exact @GlobalTheory.ClassFin.compact_subset_finite_leftCosets | exact GlobalTheory.ClassFin.compact_subset_finite_leftCosets | (intros; apply GlobalTheory.ClassFin.compact_subset_finite_leftCosets <;> assumption)
