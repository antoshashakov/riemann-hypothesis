module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finitely_many_open_subgroups_bounded_index : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ Module.finrank F E ≤ N}.Finite) → ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) | IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | exact GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite <;> assumption)
