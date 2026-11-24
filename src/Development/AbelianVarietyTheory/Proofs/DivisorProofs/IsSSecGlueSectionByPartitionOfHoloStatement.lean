module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSSecGlueSectionByPartitionOfHolo
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.isSSec_glueSectionByPartition_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → A.IsSSec (A.kap + la) (glue C la u) := by
  first | exact @GlobalTheory.OTY.glue_isSSec_of_holo | exact GlobalTheory.OTY.glue_isSSec_of_holo | (intros; apply GlobalTheory.OTY.glue_isSSec_of_holo <;> assumption)
