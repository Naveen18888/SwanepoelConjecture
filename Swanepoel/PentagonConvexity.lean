module
public import Swanepoel.PentagonFaceBoundary
public import Mathlib.Analysis.Normed.Module.Normalize
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem three_unit_chain_inner_gt_neg_half (a b c : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    (hab : (1/2:ℝ) < inner ℝ a b) (hbc : (1/2:ℝ) < inner ℝ b c) :
    (-1/2:ℝ) < inner ℝ a c := by
  have hba : inner ℝ b a=inner ℝ a b := real_inner_comm _ _
  have hpr : 1 < inner ℝ b (a+c) := by
    rw [inner_add_right,hba]
    linarith
  have hbound := real_inner_le_norm b (a+c)
  rw [hb,one_mul] at hbound
  have hn : 1<‖a+c‖ := lt_of_lt_of_le hpr hbound
  have hs := norm_add_sq_real a c
  rw [ha,hc] at hs
  nlinarith [sq_nonneg (‖a+c‖-1)]

theorem four_unit_chain_common_half_plane (a b c d : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) (hd : ‖d‖=1)
    (hab : (1/2:ℝ) < inner ℝ a b) (hbc : (1/2:ℝ) < inner ℝ b c)
    (hcd : (1/2:ℝ) < inner ℝ c d) :
    0 < inner ℝ (b+c) a ∧ 0 < inner ℝ (b+c) b ∧
      0 < inner ℝ (b+c) c ∧ 0 < inner ℝ (b+c) d := by
  have hac := three_unit_chain_inner_gt_neg_half a b c ha hb hc hab hbc
  have hbd := three_unit_chain_inner_gt_neg_half b c d hb hc hd hbc hcd
  simp only [inner_add_left,real_inner_self_eq_norm_sq,hb,hc]
  have hba : inner ℝ b a=inner ℝ a b := real_inner_comm _ _
  have hca : inner ℝ c a=inner ℝ a c := real_inner_comm _ _
  have hcb : inner ℝ c b=inner ℝ b c := real_inner_comm _ _
  simp only [hba,hca,hcb]
  constructor
  · linarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem normalized_inner_gt_half (x y : Plane) (hx : x≠0) (hy : y≠0)
    (h : ‖x‖*‖y‖/2 < inner ℝ x y) :
    (1/2:ℝ) < inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y) := by
  rw [NormedSpace.normalize,NormedSpace.normalize,real_inner_smul_left,real_inner_smul_right]
  have heq : ‖x‖⁻¹*(‖y‖⁻¹*inner ℝ x y)=inner ℝ x y/(‖x‖*‖y‖) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq]
  exact (lt_div_iff₀ (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))).mpr (by nlinarith)

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem vertex_strict_support (ht : G.TriangleFree) (i : Fin 5) :
    ∃ b : Plane, ∀ j : Fin 5, j≠i → 0 < inner ℝ b (G.point (P.vertex j)-G.point (P.vertex i)) := by
  let view (j : Fin 5) := G.point (P.vertex (i+j))-G.point (P.vertex i)
  let ray (j : Fin 5) := NormedSpace.normalize (view j)
  have hv (j : Fin 5) (hj : j≠0) : view j≠0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hidx := P.vertex_injective (G.point_injective heq)
    have hz : j=0 := add_left_cancel (show i+j=i+0 by simpa only [add_zero] using hidx)
    exact hj hz
  have hu (j : Fin 5) (hj : j≠0) : ‖ray j‖=1 := NormedSpace.norm_normalize (hv j hj)
  have hstep (j : Fin 5) (hj : j=1 ∨ j=2 ∨ j=3) :
      (1/2:ℝ) < inner ℝ (ray j) (ray (j+1)) := by
    have hj0 : j≠0 := by rcases hj with rfl | rfl | rfl <;> decide
    have hj1 : j+1≠0 := by rcases hj with rfl | rfl | rfl <;> decide
    apply normalized_inner_gt_half _ _ (hv j hj0) (hv (j+1) hj1)
    simpa only [view,add_assoc] using P.opposite_side_view_inner ht i j hj
  have hhalf := four_unit_chain_common_half_plane (ray 1) (ray 2) (ray 3) (ray 4)
    (hu 1 (by decide)) (hu 2 (by decide)) (hu 3 (by decide)) (hu 4 (by decide))
    (hstep 1 (Or.inl rfl)) (hstep 2 (Or.inr (Or.inl rfl))) (hstep 3 (Or.inr (Or.inr rfl)))
  let b := ray 2+ray 3
  refine ⟨b,?_⟩
  have hraw (j : Fin 5) (h : 0 < inner ℝ b (ray j)) : 0 < inner ℝ b (view j) := by
    change 0 < inner ℝ b (NormedSpace.normalize (view j)) at h
    rw [NormedSpace.normalize,real_inner_smul_right] at h
    exact (mul_pos_iff.mp h).resolve_right (fun hn => (inv_nonneg.mpr (norm_nonneg _)).not_gt hn.1) |>.2
  intro j hji
  have hj : j=i+1 ∨ j=i+2 ∨ j=i+3 ∨ j=i+4 := by
    fin_cases i <;> fin_cases j <;> norm_num at *
  rcases hj with rfl | rfl | rfl | rfl
  · exact hraw 1 hhalf.1
  · exact hraw 2 hhalf.2.1
  · exact hraw 3 hhalf.2.2.1
  · exact hraw 4 hhalf.2.2.2

theorem vertex_not_mem_convexHull_others (ht : G.TriangleFree) (i : Fin 5) :
    G.point (P.vertex i)∉convexHull ℝ
      (Set.range (fun j : {j : Fin 5 // j≠i} => G.point (P.vertex j.val))) := by
  obtain ⟨b,hb⟩ := P.vertex_strict_support ht i
  let H : Set Plane := {z | inner ℝ b (G.point (P.vertex i)) < inner ℝ b z}
  have hH : Convex ℝ H :=
    (convex_Ioi (inner ℝ b (G.point (P.vertex i)))).linear_preimage (innerSL ℝ b).toLinearMap
  have hsub : Set.range (fun j : {j : Fin 5 // j≠i} => G.point (P.vertex j.val))⊆H := by
    rintro _ ⟨j,rfl⟩
    have h := hb j.val j.property
    rw [inner_sub_right] at h
    exact sub_pos.mp h
  intro h
  have hbad := (convexHull_min hsub hH) h
  change inner ℝ b (G.point (P.vertex i)) < inner ℝ b (G.point (P.vertex i)) at hbad
  exact lt_irrefl _ hbad

end PentagonFaceBoundary
end Swanepoel
