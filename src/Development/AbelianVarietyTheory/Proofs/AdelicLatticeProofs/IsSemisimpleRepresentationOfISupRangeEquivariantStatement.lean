module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range <;> assumption)
