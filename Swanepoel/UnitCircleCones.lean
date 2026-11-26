module
public import Swanepoel.PentagonAngularIntervals
public import Swanepoel.PentagonConeAccounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def unitAngleVector (θ : ℝ) : Plane :=
  WithLp.toLp 2 ![Real.cos (Real.pi/3*θ),Real.sin (Real.pi/3*θ)]

theorem unitAngleVector_norm (θ : ℝ) : ‖unitAngleVector θ‖=1 := by
  have h : ‖unitAngleVector θ‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [unitAngleVector,Fin.sum_univ_two]
  nlinarith only [h,norm_nonneg (unitAngleVector θ)]

theorem unitAngleVector_inner (a b : ℝ) :
    inner ℝ (unitAngleVector a) (unitAngleVector b)=Real.cos (Real.pi/3*(b-a)) := by
  rw [mul_sub,Real.cos_sub]
  simp [unitAngleVector,PiLp.inner_apply,Fin.sum_univ_two]

theorem unitAngleVector_cross (a b : ℝ) :
    cross2 (unitAngleVector a) (unitAngleVector b)=Real.sin (Real.pi/3*(b-a)) := by
  rw [mul_sub,Real.sin_sub]
  simp [unitAngleVector,cross2]
  ring

theorem unitAngleVector_half_open {a θ : ℝ} (hθ : a-1<θ ∧ θ≤a+1) :
    HalfOpen120Cone (unitAngleVector a) (unitAngleVector θ) := by
  let d := Real.pi/3*(θ-a)
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have hd0 : -(Real.pi/3)<d := by dsimp [d]; nlinarith only [hθ.1,hp]
  have hd1 : d≤Real.pi/3 := by dsimp [d]; nlinarith only [hθ.2,hp]
  rw [HalfOpen120Cone,unitAngleVector_inner,unitAngleVector_cross]
  change (1/2:ℝ)<Real.cos d ∨ (Real.cos d=1/2 ∧ 0<Real.sin d)
  by_cases he : d=Real.pi/3
  · right
    rw [he,Real.cos_pi_div_three]
    exact ⟨rfl,Real.sin_pos_of_pos_of_lt_pi hp (by linarith [Real.pi_pos])⟩
  · left
    have hlt : d<Real.pi/3 := lt_of_le_of_ne hd1 he
    have habs : |d|<Real.pi/3 := abs_lt.mpr ⟨hd0,hlt⟩
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg d)
      (show Real.pi/3≤Real.pi by linarith [Real.pi_pos]) habs
    have heven : Real.cos |d|=Real.cos d := by
      rcases le_total 0 d with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h,Real.cos_neg]
    rwa [Real.cos_pi_div_three,heven] at hc

theorem unitAngleVector_separated_axes (ρ s t : ℝ) (hst : t-s=1 ∨ t-s=2) :
    |inner ℝ (unitAngleVector (ρ+s+1)) (unitAngleVector (ρ+t+1))|=1/2 := by
  rw [unitAngleVector_inner,show (ρ+t+1)-(ρ+s+1)=t-s by ring]
  rcases hst with h | h
  · rw [h,mul_one,Real.cos_pi_div_three]
    norm_num
  · rw [h,show Real.pi/3*2=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]
    norm_num

def angularConeAxes (ρ s t : ℝ) (b : Bool) : Plane :=
  unitAngleVector (ρ+(if b then t else s)+1)

theorem angular120Slots_le_coneSlots (ρ s t θ : ℝ) :
    angular120Slots s t θ≤twoConeSlots (angularConeAxes ρ s t) (unitAngleVector (ρ+θ)) := by
  have hslot (u : ℝ) :
      (if θ∈Set.Ioc u (u+2) then 1 else 0 : ℕ)≤
        (if HalfOpen120Cone (unitAngleVector (ρ+u+1)) (unitAngleVector (ρ+θ)) then 1 else 0) := by
    by_cases h : θ∈Set.Ioc u (u+2)
    · have hc := unitAngleVector_half_open
        (a := ρ+u+1) (θ := ρ+θ) ⟨by linarith [h.1],by linarith [h.2]⟩
      simp only [ite_eq_left h,ite_eq_left hc,le_refl]
    · simp only [ite_eq_right h,Nat.zero_le]
  exact Nat.add_le_add (hslot s) (hslot t)

theorem pentagon_angular_cone_cover (ρ a b g : ℝ)
    (ha0 : 0<a) (ha2 : a<2) (hb0 : 0<b) (hb2 : b<2)
    (hg0 : 0<g) (hg2 : g<2) (hag : 2≤a+g) (hbg : 2≤b+g)
    (habg : 3≤a+b+g) :
    ∃ axis : Bool→Plane,(∀ c,‖axis c‖=1) ∧ |inner ℝ (axis false) (axis true)|≤1/2 ∧
      ∀ (θ : ℝ) (k : ℕ),k≤2 → (0<k → pentagonSingleAngles g θ) →
        (k=2 → pentagonDoubleAngles a b g θ) → k≤twoConeSlots axis (unitAngleVector (ρ+θ)) := by
  obtain ⟨s,t,hst,hslots⟩ := pentagon_angular_multiplicity_bound a b g ha0 ha2 hb0 hb2 hg0 hg2 hag hbg habg
  refine ⟨angularConeAxes ρ s t,fun c => unitAngleVector_norm _,?_,?_⟩
  · exact (unitAngleVector_separated_axes ρ s t hst).le
  · intro θ k hk hs hd
    exact (hslots θ k hk hs hd).trans (angular120Slots_le_coneSlots ρ s t θ)

end Swanepoel
