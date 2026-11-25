module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.galoisRep_entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.CoefField.entries_mem_of_finset | exact GlobalTheory.CoefField.entries_mem_of_finset | (intros; apply GlobalTheory.CoefField.entries_mem_of_finset <;> assumption)
