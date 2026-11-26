module
public import Swanepoel.UnitCircleCones
public import Mathlib.Algebra.Order.ToIntervalMod
@[expose] public section

noncomputable section
namespace Swanepoel

theorem unitAngleVector_periodic : Function.Periodic unitAngleVector 6 := by
  intro θ
  ext i
  fin_cases i <;> simp [unitAngleVector,
    show Real.pi/3*(θ+6)=Real.pi/3*θ+2*Real.pi by ring,
    Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem exists_unitAngleVector (v : Plane) (hv : ‖v‖=1) : ∃ θ : ℝ,unitAngleVector θ=v := by
  let θ := 3*Complex.arg (planeComplex v)/Real.pi
  have hθ : Real.pi/3*θ=Complex.arg (planeComplex v) := by
    dsimp [θ]
    field_simp
  have hn : ‖planeComplex v‖=1 := (planeComplex_norm v).trans hv
  have hc := Complex.norm_mul_cos_arg (planeComplex v)
  have hs := Complex.norm_mul_sin_arg (planeComplex v)
  rw [hn,one_mul] at hc hs
  refine ⟨θ,?_⟩
  ext i
  fin_cases i
  · change Real.cos (Real.pi/3*θ)=v 0
    rw [hθ,hc]
    rfl
  · change Real.sin (Real.pi/3*θ)=v 1
    rw [hθ,hs]
    rfl

theorem exists_relative_unitAngleVector (v : Plane) (hv : ‖v‖=1) (ρ a : ℝ) :
    ∃ θ : ℝ,θ∈Set.Ioc a (a+6) ∧ unitAngleVector (ρ+θ)=v := by
  obtain ⟨τ,hτ⟩ := exists_unitAngleVector v hv
  let hp : (0:ℝ)<6 := by norm_num
  let θ := toIocMod hp a (τ-ρ)
  have hmod : ρ+θ=τ-toIocDiv hp a (τ-ρ) • (6:ℝ) := by
    dsimp [θ]
    rw [toIocMod]
    abel
  refine ⟨θ,toIocMod_mem_Ioc hp a (τ-ρ),?_⟩
  rw [hmod,unitAngleVector_periodic.sub_zsmul_eq,hτ]

theorem quarterTurn_unitAngleVector (ρ : ℝ) :
    quarterTurn (unitAngleVector ρ)=unitAngleVector (ρ+3/2) := by
  ext i
  fin_cases i <;> simp [unitAngleVector,quarterTurn,
    show Real.pi/3*(ρ+3/2)=Real.pi/3*ρ+Real.pi/2 by ring,
    Real.cos_add_pi_div_two,Real.sin_add_pi_div_two]

theorem cos_two_pi_div_three_value : Real.cos (2*Real.pi/3)= -1/2 := by
  rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
  ring

theorem clockwise_unitAngle_gap (ρ : ℝ) (v : Plane) (hv : ‖v‖=1)
    (hcross : cross2 (unitAngleVector ρ) v<0)
    (hinner : (-1/2:ℝ) < inner ℝ (unitAngleVector ρ) v) :
    ∃ g : ℝ,0<g ∧ g<2 ∧ unitAngleVector (ρ-g)=v := by
  obtain ⟨θ,hθ,hphase⟩ := exists_relative_unitAngleVector v hv ρ (-3)
  have hlo : (-3:ℝ)<θ := hθ.1
  have hhi : θ≤3 := by linarith only [hθ.2]
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have hsin : Real.sin (Real.pi/3*θ)<0 := by
    rw [← hphase,unitAngleVector_cross,add_sub_cancel_left] at hcross
    exact hcross
  have hcos : (-1/2:ℝ)<Real.cos (Real.pi/3*θ) := by
    rw [← hphase,unitAngleVector_inner,add_sub_cancel_left] at hinner
    exact hinner
  have hneg : θ<0 := by
    by_contra hn
    have hnn := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0≤Real.pi/3*θ by nlinarith only [hp,le_of_not_gt hn])
      (show Real.pi/3*θ≤Real.pi by nlinarith only [hp,hhi])
    linarith only [hsin,hnn]
  have htwo : -θ<2 := by
    by_contra hn
    have hbound := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0≤2*Real.pi/3 by positivity)
      (show Real.pi/3*(-θ)≤Real.pi by nlinarith only [hp,hlo])
      (show 2*Real.pi/3≤Real.pi/3*(-θ) by nlinarith only [hp,le_of_not_gt hn])
    rw [cos_two_pi_div_three_value,show Real.pi/3*(-θ)= -(Real.pi/3*θ) by ring,Real.cos_neg] at hbound
    linarith only [hcos,hbound]
  exact ⟨-θ,neg_pos.mpr hneg,htwo,by simpa only [sub_neg_eq_add] using hphase⟩

theorem counterclockwise_unitAngle_gap (ρ : ℝ) (v : Plane) (hv : ‖v‖=1)
    (hcross : 0<cross2 (unitAngleVector ρ) v)
    (hinner : (-1/2:ℝ) < inner ℝ (unitAngleVector ρ) v) :
    ∃ g : ℝ,0<g ∧ g<2 ∧ unitAngleVector (ρ+g)=v := by
  obtain ⟨θ,hθ,hphase⟩ := exists_relative_unitAngleVector v hv ρ (-3)
  have hlo : (-3:ℝ)<θ := hθ.1
  have hhi : θ≤3 := by linarith only [hθ.2]
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have hsin : 0<Real.sin (Real.pi/3*θ) := by
    rw [← hphase,unitAngleVector_cross,add_sub_cancel_left] at hcross
    exact hcross
  have hcos : (-1/2:ℝ)<Real.cos (Real.pi/3*θ) := by
    rw [← hphase,unitAngleVector_inner,add_sub_cancel_left] at hinner
    exact hinner
  have hpos : 0<θ := by
    by_contra hn
    have hnn := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (show Real.pi/3*θ≤0 by nlinarith only [hp,le_of_not_gt hn])
      (show -Real.pi≤Real.pi/3*θ by nlinarith only [hp,hlo])
    linarith only [hsin,hnn]
  have htwo : θ<2 := by
    by_contra hn
    have hbound := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0≤2*Real.pi/3 by positivity)
      (show Real.pi/3*θ≤Real.pi by nlinarith only [hp,hhi])
      (show 2*Real.pi/3≤Real.pi/3*θ by nlinarith only [hp,le_of_not_gt hn])
    rw [cos_two_pi_div_three_value] at hbound
    linarith only [hcos,hbound]
  exact ⟨θ,hpos,htwo,hphase⟩

theorem unitAngleVector_inner_pos_of_gap (a θ : ℝ) (h : a-3/2<θ ∧ θ<a+3/2) :
    0 < inner ℝ (unitAngleVector a) (unitAngleVector θ) := by
  rw [unitAngleVector_inner]
  apply Real.cos_pos_of_mem_Ioo
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  constructor <;> nlinarith only [hp,h.1,h.2]

theorem two_le_of_cos_le_neg_half (t : ℝ) (ht : 0<t)
    (hcos : Real.cos (Real.pi/3*t)≤ -1/2) : 2≤t := by
  by_contra hn
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show 0≤Real.pi/3*t by positivity)
    (show 2*Real.pi/3≤Real.pi by linarith [Real.pi_pos])
    (show Real.pi/3*t<2*Real.pi/3 by nlinarith only [hp,lt_of_not_ge hn])
  rw [cos_two_pi_div_three_value] at hlt
  linarith only [hcos,hlt]

end Swanepoel
