/-
══════════════════════════════════════════════════════════════════════════════
  §3. Main Theorem: Uniqueness of A₅ Holonomy in SO(3)
══════════════════════════════════════════════════════════════════════════════

  File     : A5CosmicNecessity/Section3_MainTheorem.lean
  Author   : M. Numagaki
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

import A5CosmicNecessity.SolvabilityBelow60

set_option maxRecDepth 4000

namespace CosmicNecessity


/-!
══════════════════════════════════════════════════════════════════════════════
  §3
══════════════════════════════════════════════════════════════════════════════
-/

section Foundations

theorem A5_perfect_s3 :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))),
      (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤ := by
  let G := alternatingGroup (Fin 5)
  haveI hsimple : IsSimpleGroup G := alternatingGroup.isSimpleGroup_five
  have h_ne_bot : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a b : G, a * b = b * a := by
      have hcenter : Subgroup.center G = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top (G := G)).mp hbot
      intro a b
      have ha : a ∈ Subgroup.center G := by simp [hcenter]
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    exact A5_not_solvable ((IsSimpleGroup.comm_iff_isSolvable).mp hcomm)
  have h_bot_or_top : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ ∨ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ :=
    Subgroup.Normal.eq_bot_or_eq_top
      (H := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
      (Subgroup.commutator_normal ⊤ ⊤)
  exact h_bot_or_top.resolve_left h_ne_bot

end Foundations

section SolvableImageOpacity

structure SolvableProbe (G : Type*) [Group G] where
  Q : Type*
  [grpQ : Group Q]
  [finQ : Fintype Q]
  [solQ : IsSolvable Q]
  π : G →* Q

attribute [instance] SolvableProbe.grpQ SolvableProbe.finQ SolvableProbe.solQ


theorem solvable_opacity
    {G : Type*} [Group G] [Fintype G]
    (h_ns : ¬ IsSolvable G) (probe : SolvableProbe G) :
    ¬ Function.Injective probe.π := by
  intro h_inj
  exact h_ns (solvable_of_injective_to_solvable probe.π h_inj)

theorem solvable_of_injective_probe
    {G : Type*} [Group G] [Fintype G]
    (probe : SolvableProbe G)
    (h_inj : Function.Injective probe.π) :
    IsSolvable G :=
  solvable_of_injective_to_solvable probe.π h_inj

theorem simple_nonsolvable_total_opacity
    {G : Type*} [Group G] [Fintype G]
    (h_simple : IsSimpleGroup G) (h_ns : ¬ IsSolvable G)
    (probe : SolvableProbe G) :
    probe.π.ker = ⊤ := by
  haveI := h_simple
  have h_bot_or_top : probe.π.ker = ⊥ ∨ probe.π.ker = ⊤ :=
    Subgroup.Normal.eq_bot_or_eq_top
      (H := probe.π.ker)
      inferInstance
  rcases h_bot_or_top with hbot | htop
  · exfalso
    have h_inj : Function.Injective probe.π := by
      intro x y hxy
      have hmem : x * y⁻¹ ∈ probe.π.ker := by
        simp [MonoidHom.mem_ker, map_mul, map_inv, hxy]
      rw [hbot] at hmem
      have heq : x * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
      calc x = x * y⁻¹ * y := by group
           _ = 1 * y := by rw [heq]
           _ = y := one_mul y
    exact solvable_opacity h_ns probe h_inj
  · exact htop

theorem A5_probe_ker_eq_top
    (probe : SolvableProbe (alternatingGroup (Fin 5))) :
    probe.π.ker = ⊤ :=
  simple_nonsolvable_total_opacity A5_is_simple A5_not_solvable probe


theorem A5_probe_trivializes
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    (g : alternatingGroup (Fin 5)) :
    probe.π g = 1 := by
  have h_ker_top := A5_probe_ker_eq_top probe
  have h_mem : g ∈ probe.π.ker := by
    rw [h_ker_top]; exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.mp h_mem

theorem A5_probe_cannot_distinguish
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    (g h : alternatingGroup (Fin 5)) :
    probe.π g = probe.π h := by
  rw [A5_probe_trivializes probe g, A5_probe_trivializes probe h]


theorem criticality_theorem :
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G < 60 → IsSolvable G) ∧
    (¬ IsSolvable (alternatingGroup (Fin 5)) ∧
     Fintype.card (alternatingGroup (Fin 5)) = 60) :=
  ⟨fun _ _ _ h => groups_below_60_solvable h,
   ⟨A5_not_solvable, A5_card⟩⟩


theorem minimal_barrier_basis :
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G < 60 → IsSolvable G) ∧
    (Fintype.card (alternatingGroup (Fin 5)) = 60 ∧
     ¬ IsSolvable (alternatingGroup (Fin 5)) ∧
     IsSimpleGroup (alternatingGroup (Fin 5))) ∧
    (∀ N : ℕ, 60 ^ N ≥ 2 ^ (5 * N)) :=
  ⟨fun G _ _ h => groups_below_60_solvable h,
   ⟨A5_card, A5_not_solvable, A5_is_simple⟩,
   fun N => by
     have : 2 ^ (5 * N) = (2 ^ 5) ^ N := by rw [Nat.pow_mul]
     rw [this]; exact Nat.pow_le_pow_left (by norm_num : 2 ^ 5 ≤ 60) N⟩

end SolvableImageOpacity


/-!
══════════════════════════════════════════════════════════════════════════════
  §3.2.
══════════════════════════════════════════════════════════════════════════════
-/

section MainTheorem

theorem S4_not_perfect_s3 :
    ⁅(⊤ : Subgroup (Equiv.Perm (Fin 4))),
      (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ ≠ ⊤ := by
  apply not_perfect_of_solvable_nontrivial S4_solvable
  have : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by native_decide
  omega

theorem A4_not_perfect_s3 :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 4))),
      (⊤ : Subgroup (alternatingGroup (Fin 4)))⁆ ≠ ⊤ := by
  apply not_perfect_of_solvable_nontrivial A4_solvable
  have : Fintype.card (alternatingGroup (Fin 4)) = 12 := by native_decide
  omega

theorem H3_perfectness_classification_s3 :
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤) ∧
    (⁅(⊤ : Subgroup (Equiv.Perm (Fin 4))), (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ ≠ ⊤) ∧
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 4))), (⊤ : Subgroup (alternatingGroup (Fin 4)))⁆ ≠ ⊤) :=
  ⟨A5_perfect_s3, S4_not_perfect_s3, A4_not_perfect_s3⟩


theorem main_theorem :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true ∧ kleintypePassesH3 kt = true →
    kt = KleinType.icosahedral := by
  intro kt ⟨h2, h3⟩
  match kt with
  | .cyclic n    => simp [kleintypePassesH2] at h2
  | .dihedral n  => simp [kleintypePassesH2] at h2
  | .tetrahedral => simp [kleintypePassesH3] at h3
  | .octahedral  => simp [kleintypePassesH3] at h3
  | .icosahedral => rfl

theorem main_theorem_converse :
    kleintypePassesH2 KleinType.icosahedral = true ∧
    kleintypePassesH3 KleinType.icosahedral = true :=
  ⟨rfl, rfl⟩

theorem main_theorem_unique :
    ∃! kt : KleinType,
    (kt = KleinType.tetrahedral ∨ kt = KleinType.octahedral ∨
     kt = KleinType.icosahedral) ∧
    kleintypePassesH3 kt = true := by
  refine ⟨KleinType.icosahedral, ⟨Or.inr (Or.inr rfl), rfl⟩, ?_⟩
  intro kt' ⟨h_poly, h3⟩
  rcases h_poly with rfl | rfl | rfl
  · simp [kleintypePassesH3] at h3
  · simp [kleintypePassesH3] at h3
  · rfl

end MainTheorem


/-!
══════════════════════════════════════════════════════════════════════════════
  §3.3.
══════════════════════════════════════════════════════════════════════════════
-/

section AlternativeConditions

def kleintypePassesH3star : KleinType → Bool
  | KleinType.cyclic n    => n ≤ 1
  | KleinType.dihedral _  => false
  | KleinType.tetrahedral => false
  | KleinType.octahedral  => false
  | KleinType.icosahedral => true

theorem corollary_H3star :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true ∧ kleintypePassesH3star kt = true →
    kt = KleinType.icosahedral := by
  intro kt ⟨h2, h3s⟩
  match kt with
  | .cyclic n    => simp [kleintypePassesH2] at h2
  | .dihedral n  => simp [kleintypePassesH2] at h2
  | .tetrahedral => simp [kleintypePassesH3star] at h3s
  | .octahedral  => simp [kleintypePassesH3star] at h3s
  | .icosahedral => rfl

theorem H3_iff_H3star_on_polyhedral :
    (kleintypePassesH3 KleinType.tetrahedral =
     kleintypePassesH3star KleinType.tetrahedral) ∧
    (kleintypePassesH3 KleinType.octahedral =
     kleintypePassesH3star KleinType.octahedral) ∧
    (kleintypePassesH3 KleinType.icosahedral =
     kleintypePassesH3star KleinType.icosahedral) := by
  simp [kleintypePassesH3, kleintypePassesH3star]

theorem H3star_implies_H3_basis :
    IsSolvable (alternatingGroup (Fin 4)) ∧
    IsSolvable (Equiv.Perm (Fin 4)) ∧
    ¬ IsSolvable (alternatingGroup (Fin 5)) :=
  ⟨A4_solvable, S4_solvable, A5_not_solvable⟩


theorem corollary_maximality :
    (KleinType.order .tetrahedral < KleinType.order .octahedral) ∧
    (KleinType.order .octahedral < KleinType.order .icosahedral) ∧
    (Fintype.card (alternatingGroup (Fin 4)) <
     Fintype.card (Equiv.Perm (Fin 4))) ∧
    (Fintype.card (Equiv.Perm (Fin 4)) <
     Fintype.card (alternatingGroup (Fin 5))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [KleinType.order]
  · simp [KleinType.order]
  · have h1 := A4_card; have h2 := S4_card; omega
  · have h1 := S4_card; have h2 := A5_card; omega

theorem maximality_selects_A5 :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true →
    KleinType.order kt ≤ KleinType.order .icosahedral := by
  intro kt h2
  match kt with
  | .cyclic n    => simp [kleintypePassesH2] at h2
  | .dihedral n  => simp [kleintypePassesH2] at h2
  | .tetrahedral => simp [KleinType.order]
  | .octahedral  => simp [KleinType.order]
  | .icosahedral => exact le_refl _


def kleintypePassesH3double : KleinType → Bool
  | KleinType.cyclic _    => false
  | KleinType.dihedral _  => false
  | KleinType.tetrahedral => false
  | KleinType.octahedral  => false
  | KleinType.icosahedral => true

theorem corollary_nonsolvability :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true ∧ kleintypePassesH3double kt = true →
    kt = KleinType.icosahedral := by
  intro kt ⟨h2, h3d⟩
  match kt with
  | .cyclic n    => simp [kleintypePassesH2] at h2
  | .dihedral n  => simp [kleintypePassesH2] at h2
  | .tetrahedral => simp [kleintypePassesH3double] at h3d
  | .octahedral  => simp [kleintypePassesH3double] at h3d
  | .icosahedral => rfl

theorem nonsolvability_classification :
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    IsSolvable (alternatingGroup (Fin 4)) ∧
    IsSolvable (Equiv.Perm (Fin 4)) :=
  ⟨A5_not_solvable, A4_solvable, S4_solvable⟩


def kleintypePassesH3triple : KleinType → Bool
  | KleinType.cyclic n    => (5 ∣ n)
  | KleinType.dihedral _  => false
  | KleinType.tetrahedral => false
  | KleinType.octahedral  => false
  | KleinType.icosahedral => true

theorem A4_no_order_5_element :
    ∀ g : alternatingGroup (Fin 4), orderOf g ≠ 5 := by
  intro g h
  have h_dvd : orderOf g ∣ Fintype.card (alternatingGroup (Fin 4)) :=
    orderOf_dvd_card
  rw [A4_card] at h_dvd
  rw [h] at h_dvd
  exact absurd h_dvd (by decide)

theorem S4_no_order_5_element :
    ∀ g : Equiv.Perm (Fin 4), orderOf g ≠ 5 := by
  intro g h
  have h_dvd : orderOf g ∣ Fintype.card (Equiv.Perm (Fin 4)) :=
    orderOf_dvd_card
  rw [S4_card] at h_dvd
  rw [h] at h_dvd
  exact absurd h_dvd (by decide)

theorem A5_has_order_5_element :
    ∃ g : alternatingGroup (Fin 5), orderOf g = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, orderOf_eq_prime ?_ ?_⟩
  · exact Subtype.ext (by decide)
  · intro h; exact absurd (Subtype.ext_iff.mp h) (by decide)

theorem corollary_order5 :
    (∀ g : alternatingGroup (Fin 4), orderOf g ≠ 5) ∧
    (∀ g : Equiv.Perm (Fin 4), orderOf g ≠ 5) ∧
    (∃ g : alternatingGroup (Fin 5), orderOf g = 5) :=
  ⟨A4_no_order_5_element, S4_no_order_5_element, A5_has_order_5_element⟩

theorem corollary_order5_klein :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true ∧ kleintypePassesH3triple kt = true →
    kt = KleinType.icosahedral := by
  intro kt ⟨h2, h3t⟩
  match kt with
  | .cyclic n    => simp [kleintypePassesH2] at h2
  | .dihedral n  => simp [kleintypePassesH2] at h2
  | .tetrahedral => simp [kleintypePassesH3triple] at h3t
  | .octahedral  => simp [kleintypePassesH3triple] at h3t
  | .icosahedral => rfl


theorem five_conditions_converge :
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3 kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3star kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3double kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3triple kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true →
     KleinType.order kt ≤ KleinType.order .icosahedral) :=
  ⟨main_theorem,
   corollary_H3star,
   corollary_nonsolvability,
   corollary_order5_klein,
   maximality_selects_A5⟩

end AlternativeConditions


/-!
══════════════════════════════════════════════════════════════════════════════
  §3.5.
══════════════════════════════════════════════════════════════════════════════
-/

section StrengthAndLimitations

theorem elimination_targets_disjoint_s3 :
    (∀ n, kleintypePassesH2 (KleinType.cyclic n) = false) ∧
    (∀ n, kleintypePassesH2 (KleinType.dihedral n) = false) ∧
    (kleintypePassesH2 KleinType.tetrahedral = true) ∧
    (kleintypePassesH2 KleinType.octahedral = true) ∧
    (kleintypePassesH3 KleinType.tetrahedral = false) ∧
    (kleintypePassesH3 KleinType.octahedral = false) := by
  exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩


theorem H1_H2_insufficient_s3 :
    kleintypePassesH2 KleinType.tetrahedral = true ∧
    kleintypePassesH2 KleinType.octahedral = true ∧
    kleintypePassesH2 KleinType.icosahedral = true ∧
    KleinType.tetrahedral ≠ KleinType.octahedral ∧
    KleinType.octahedral ≠ KleinType.icosahedral ∧
    KleinType.tetrahedral ≠ KleinType.icosahedral := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide

theorem H1_H3_insufficient_s3 :
    kleintypePassesH3 (KleinType.cyclic 0) = true ∧
    kleintypePassesH3 (KleinType.cyclic 1) = true ∧
    kleintypePassesH3 KleinType.icosahedral = true ∧
    KleinType.cyclic 0 ≠ KleinType.icosahedral := by
  simp [kleintypePassesH3]

theorem H2_H3_sufficient_within_Klein :
    ∀ kt : KleinType,
    kleintypePassesH2 kt = true ∧ kleintypePassesH3 kt = true →
    kt = KleinType.icosahedral :=
  main_theorem

theorem all_three_conditions_necessary :
    (∃ kt₁ kt₂ : KleinType,
     kt₁ ≠ kt₂ ∧
     kleintypePassesH2 kt₁ = true ∧ kleintypePassesH2 kt₂ = true) ∧
    (∃ kt₁ kt₂ : KleinType,
     kt₁ ≠ kt₂ ∧
     kleintypePassesH3 kt₁ = true ∧ kleintypePassesH3 kt₂ = true) ∧
    (∀ kt : KleinType,
     kleintypePassesH2 kt = true ∧ kleintypePassesH3 kt = true →
     kt = KleinType.icosahedral) := by
  refine ⟨?_, ?_, main_theorem⟩
  · exact ⟨.tetrahedral, .icosahedral, by decide, rfl, rfl⟩
  · exact ⟨.cyclic 0, .icosahedral, by decide,
           by simp [kleintypePassesH3], rfl⟩

end StrengthAndLimitations


/-!
══════════════════════════════════════════════════════════════════════════════
  §3.6.
══════════════════════════════════════════════════════════════════════════════
-/

section VerificationSummary

theorem section3_verification_summary :
    (Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    IsSimpleGroup (alternatingGroup (Fin 5)) ∧
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤) ∧
    (∀ probe : SolvableProbe (alternatingGroup (Fin 5)),
     probe.π.ker = ⊤) ∧
    (∀ (G : Type) [Group G] [Fintype G],
      Fintype.card G < 60 → IsSolvable G) ∧
    (∀ N : ℕ, 60 ^ N ≥ 2 ^ (5 * N)) ∧
    (∀ kt : KleinType,
     kleintypePassesH2 kt = true ∧ kleintypePassesH3 kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3star kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3double kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ kt, kleintypePassesH2 kt = true ∧ kleintypePassesH3triple kt = true →
     kt = KleinType.icosahedral) ∧
    (∀ g : alternatingGroup (Fin 4), orderOf g ≠ 5) ∧
    (∀ g : Equiv.Perm (Fin 4), orderOf g ≠ 5) ∧
    (∃ g : alternatingGroup (Fin 5), orderOf g = 5) ∧
    (∃ kt₁ kt₂ : KleinType,
     kt₁ ≠ kt₂ ∧
     kleintypePassesH2 kt₁ = true ∧ kleintypePassesH2 kt₂ = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A5_card
  · exact A5_is_simple
  · exact A5_not_solvable
  · exact A5_perfect
  · exact A5_probe_ker_eq_top
  · exact fun G _ _ h => groups_below_60_solvable h
  · exact fun N => by
      have : 2 ^ (5 * N) = (2 ^ 5) ^ N := by rw [Nat.pow_mul]
      rw [this]; exact Nat.pow_le_pow_left (by norm_num : 2 ^ 5 ≤ 60) N
  · exact main_theorem
  · exact corollary_H3star
  · exact corollary_nonsolvability
  · exact corollary_order5_klein
  · exact A4_no_order_5_element
  · exact S4_no_order_5_element
  · exact A5_has_order_5_element
  · exact ⟨.tetrahedral, .icosahedral, by decide, rfl, rfl⟩


theorem A5_bridge_to_consequences :
    (Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    IsSimpleGroup (alternatingGroup (Fin 5)) ∧
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤) ∧
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G < 60 → IsSolvable G) :=
  ⟨A5_card, A5_not_solvable, A5_is_simple, A5_perfect,
   fun _ _ _ h => groups_below_60_solvable h⟩

end VerificationSummary


end CosmicNecessity
