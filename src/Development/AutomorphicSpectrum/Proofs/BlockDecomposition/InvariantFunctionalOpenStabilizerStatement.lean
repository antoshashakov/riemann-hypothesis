module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizer
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  first | exact @GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | exact GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | (intros; apply GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser <;> assumption)
