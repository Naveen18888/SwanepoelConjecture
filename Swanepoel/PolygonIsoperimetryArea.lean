module
public import Swanepoel.PolygonIsoperimetrySpectral
public import Swanepoel.PolygonArea
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cyclicVertexMean {N : ℕ} [NeZero N] (p : ZMod N → Plane) : Plane :=
  (N : ℝ)⁻¹ • ∑ j : ZMod N, p j

theorem cyclic_mean_sub_sum_zero {N : ℕ} [NeZero N] (p : ZMod N → Plane) :
    (∑ j : ZMod N, (p j-cyclicVertexMean p)) = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [cyclicVertexMean, smul_smul, mul_inv_cancel₀ hN, one_smul, sub_self]

theorem cyclic_plane_sharp_wirtinger {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (p : ZMod N → Plane) :
    (4*Real.sin (Real.pi/N)^2)*centeredVertexEnergy p (cyclicVertexMean p) ≤
      cyclicEdgeEnergy (Equiv.addRight 1) p := by
  let f (j : ZMod N) := planeComplex (p j-cyclicVertexMean p)
  have hmean : ∑ j : ZMod N, f j = 0 := by
    change (∑ j : ZMod N, planeComplex (p j-cyclicVertexMean p)) = 0
    rw [← map_sum, cyclic_mean_sub_sum_zero, map_zero]
  have hnorm (j : ZMod N) : ‖f j‖ = ‖p j-cyclicVertexMean p‖ := planeComplex_norm _
  have hedge (j : ZMod N) : ‖f (j+1)-f j‖ = ‖p (j+1)-p j‖ := by
    change ‖planeComplex (p (j+1)-cyclicVertexMean p)-planeComplex (p j-cyclicVertexMean p)‖ = _
    rw [← map_sub, planeComplex_norm]
    congr 1
    abel
  have hw := finite_dft_sharp_wirtinger hN2 f hmean
  simp only [hnorm,hedge] at hw
  exact hw

theorem polygon_angle_bounds {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) :
    0 < Real.pi/N ∧ Real.pi/N < Real.pi/2 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  refine ⟨div_pos Real.pi_pos hN,?_⟩
  apply (div_lt_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [Real.pi_pos]

theorem finite_polygon_area_energy_bound {N : ℕ} [NeZero N] (hN3 : 3 ≤ N)
    (p : ZMod N → Plane) :
    |cyclicSignedArea (Equiv.addRight 1) p| ≤
      Real.cos (Real.pi/N)/(4*Real.sin (Real.pi/N)) * cyclicEdgeEnergy (Equiv.addRight 1) p := by
  let a := Real.pi/N
  let E := cyclicEdgeEnergy (Equiv.addRight 1) p
  let D := cyclicDoubleArea (Equiv.addRight 1) p
  have ha := polygon_angle_bounds hN3
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by dsimp [a]; linarith [ha.2,Real.pi_pos])
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo
    ⟨by dsimp [a]; linarith [ha.1,Real.pi_pos],ha.2⟩
  have hgap : 0 < 4*Real.sin a^2 := by positivity
  have hw := cyclic_plane_sharp_wirtinger (by omega : 2 ≤ N) p
  have hV : centeredVertexEnergy p (cyclicVertexMean p) ≤ (1/(4*Real.sin a^2))*E := by
    have hdiv : centeredVertexEnergy p (cyclicVertexMean p) ≤ E/(4*Real.sin a^2) :=
      (le_div_iff₀ hgap).mpr (by nlinarith [hw])
    convert hdiv using 1; ring
  have harea := cyclic_area_from_vertex_energy (Equiv.addRight 1) p (cyclicVertexMean p)
    (1/(4*Real.sin a^2)) hV
  have hcoef : 4*(1/(4*Real.sin a^2))-1 = (Real.cos a/Real.sin a)^2 := by
    field_simp [hsin.ne']
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [hcoef] at harea
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hright : 0 ≤ (Real.cos a/Real.sin a)*E := mul_nonneg (div_pos hcos hsin).le hE
  have hleft : 0 ≤ 2*|D| := by positivity
  have hsq : (2*|D|)^2 ≤ ((Real.cos a/Real.sin a)*E)^2 := by
    nlinarith [harea,sq_abs D]
  have hroot := (sq_le_sq₀ hleft hright).mp hsq
  change |D/2| ≤ Real.cos a/(4*Real.sin a)*E
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ ((Real.cos a/Real.sin a)*E)/4 := by linarith
    _ = _ := by ring

theorem polygon_cot_coefficient_le_pi {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) :
    Real.cos (Real.pi/N)/(4*Real.sin (Real.pi/N)) ≤ (N : ℝ)/(4*Real.pi) := by
  let a := Real.pi/N
  have hN : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have ha := polygon_angle_bounds hN3
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by dsimp [a]; linarith [ha.2,Real.pi_pos])
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo
    ⟨by dsimp [a]; linarith [ha.1,Real.pi_pos],ha.2⟩
  have htan := Real.le_tan ha.1.le ha.2
  rw [Real.tan_eq_sin_div_cos] at htan
  have hlow : a*Real.cos a ≤ Real.sin a := (le_div_iff₀ hcos).mp htan
  have hscaled := mul_le_mul_of_nonneg_left hlow hN.le
  have haN : (N : ℝ)*a = Real.pi := by dsimp [a]; field_simp
  rw [← mul_assoc,haN] at hscaled
  change Real.cos a/(4*Real.sin a) ≤ (N : ℝ)/(4*Real.pi)
  apply (div_le_div_iff₀ (by positivity : 0 < 4*Real.sin a)
    (by positivity : (0 : ℝ) < 4*Real.pi)).mpr
  nlinarith

theorem finite_polygon_area_le_pi_energy {N : ℕ} [NeZero N] (hN3 : 3 ≤ N)
    (p : ZMod N → Plane) :
    |cyclicSignedArea (Equiv.addRight 1) p| ≤ (N : ℝ)/(4*Real.pi) *
      cyclicEdgeEnergy (Equiv.addRight 1) p := by
  have hE : 0 ≤ cyclicEdgeEnergy (Equiv.addRight 1) p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (finite_polygon_area_energy_bound hN3 p).trans
    (mul_le_mul_of_nonneg_right (polygon_cot_coefficient_le_pi hN3) hE)

theorem finite_polygon_unit_isoperimetric {N : ℕ} [NeZero N] (hN3 : 3 ≤ N)
    (p : ZMod N → Plane) (hunit : ∀ j, ‖p (j+1)-p j‖ ≤ 1) :
    |cyclicSignedArea (Equiv.addRight 1) p| ≤ (N : ℝ)^2/(4*Real.pi) := by
  have henergy : cyclicEdgeEnergy (Equiv.addRight 1) p ≤ N := by
    calc
      _ ≤ ∑ _ : ZMod N, (1 : ℝ) := Finset.sum_le_sum (by
        intro j _
        change ‖p (j+1)-p j‖^2 ≤ 1
        have hn := norm_nonneg (p (j+1)-p j)
        have hle := hunit j
        nlinarith)
      _ = _ := by simp [ZMod.card]
  calc
    _ ≤ (N : ℝ)/(4*Real.pi)*cyclicEdgeEnergy (Equiv.addRight 1) p :=
      finite_polygon_area_le_pi_energy hN3 p
    _ ≤ (N : ℝ)/(4*Real.pi)*N := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end Swanepoel
