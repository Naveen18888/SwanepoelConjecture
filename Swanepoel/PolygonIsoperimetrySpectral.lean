module
public import Swanepoel.PolygonIsoperimetry
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_character_chord_sq {N : ℕ} [NeZero N] (k : ZMod N) :
    ‖ZMod.stdAddChar k-1‖^2 = 4*Real.sin (Real.pi*(k.val : ℝ)/N)^2 := by
  let x := Real.pi*(k.val : ℝ)/N
  have hchar : ZMod.stdAddChar k = Complex.exp ((2*x : ℝ)*Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hre : (ZMod.stdAddChar k).re = Real.cos (2*x) := by
    rw [hchar, Complex.exp_ofReal_mul_I_re]
  have hnorm : ‖ZMod.stdAddChar k‖ = 1 := AddChar.norm_apply _ _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    hnorm, Complex.normSq_one, map_one, mul_one, hre, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem sine_sq_min_on_symmetric_interval (a x : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ Real.pi/2) (hax : a ≤ x) (hxa : x ≤ Real.pi-a) :
    Real.sin a^2 ≤ Real.sin x^2 := by
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ⟨ha0,by linarith [Real.pi_pos]⟩
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc ⟨ha0.trans hax,by linarith⟩
  apply (sq_le_sq₀ hsa hsx).mpr
  by_cases hx2 : x ≤ Real.pi/2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hx2 hax
  · have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ a)
      (by linarith : Real.pi-x ≤ Real.pi/2) (by linarith : a ≤ Real.pi-x)
    simpa only [Real.sin_pi_sub] using hsin

theorem finite_character_sharp_gap {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (k : ZMod N) (hk : k ≠ 0) :
    4*Real.sin (Real.pi/N)^2 ≤ ‖ZMod.stdAddChar k-1‖^2 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hkpos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk ((ZMod.val_eq_zero k).mp h))
  have hk1 : (1 : ℝ) ≤ k.val := by exact_mod_cast hkpos
  have hkup : (k.val : ℝ)+1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt k.val_lt)
  let a := Real.pi/N
  let x := Real.pi*(k.val : ℝ)/N
  have ha0 : 0 ≤ a := (div_pos Real.pi_pos hN).le
  have ha2 : a ≤ Real.pi/2 := by
    dsimp [a]
    apply (div_le_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [Real.pi_pos]
  have hax : a ≤ x := by
    dsimp [a,x]
    apply (div_le_div_iff_of_pos_right hN).mpr
    have hp := mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le
    nlinarith
  have hxa : x ≤ Real.pi-a := by
    dsimp [a,x]
    apply (div_le_iff₀ hN).mpr
    rw [sub_mul, div_mul_cancel₀ _ hN.ne']
    have hp := mul_le_mul_of_nonneg_left hkup Real.pi_pos.le
    nlinarith
  have hsin := sine_sq_min_on_symmetric_interval a x ha0 ha2 hax hxa
  rw [finite_character_chord_sq]
  change 4*Real.sin a^2 ≤ 4*Real.sin x^2
  linarith

theorem finite_dft_sharp_wirtinger {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (f : ZMod N → ℂ) (hmean : ∑ j, f j = 0) :
    (4*Real.sin (Real.pi/N)^2)*(∑ j : ZMod N, ‖f j‖^2) ≤
      ∑ j : ZMod N, ‖f (j+1)-f j‖^2 :=
  finite_dft_wirtinger_of_spectral_gap f hmean _ (finite_character_sharp_gap hN2)

end Swanepoel
