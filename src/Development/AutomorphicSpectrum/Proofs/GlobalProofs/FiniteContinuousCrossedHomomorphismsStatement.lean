module

public import GroundTheory.ProfiniteCohomology.DiscreteModules
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteContinuousCrossedHomomorphisms
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finite_continuous_crossed_homomorphisms : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V → (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) → {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | exact GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Cocycles.finite_cocycles <;> assumption)
