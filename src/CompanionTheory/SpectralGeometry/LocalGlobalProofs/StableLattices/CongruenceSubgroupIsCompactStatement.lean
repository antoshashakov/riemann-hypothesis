module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.congruence_subgroup_is_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), IsCompact (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isCompact_congK | exact GlobalTheory.CompanionTheory.CartGL.isCompact_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isCompact_congK <;> assumption)
