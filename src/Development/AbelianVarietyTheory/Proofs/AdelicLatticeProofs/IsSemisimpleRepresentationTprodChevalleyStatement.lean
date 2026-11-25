module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod <;> assumption)
