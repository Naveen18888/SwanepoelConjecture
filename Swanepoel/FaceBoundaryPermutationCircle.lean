module
public import Swanepoel.FaceBoundaryOrder
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def ClockwiseRayBetween (u w x : Plane) : Prop :=
  if u=w then x≠u else
  if cross2 u w<0 then cross2 u x<0 ∧ 0<cross2 w x else
  if cross2 u w=0 then cross2 u x<0 else
    cross2 u x<0 ∨ 0<cross2 w x

private theorem cr_cross_swap (u w : Plane) : cross2 w u= -cross2 u w := by
  unfold cross2
  ring

private theorem cr_cross_neg_right (u w : Plane) : cross2 u (-w)= -cross2 u w := by
  unfold cross2
  simp only [PiLp.neg_apply]
  ring

private theorem cr_unit_ne_neg (u : Plane) (hu : ‖u‖=1) : u≠ -u := by
  intro h
  have hi := congrArg (inner ℝ u) h
  rw [inner_neg_right,real_inner_self_eq_norm_sq,hu] at hi
  norm_num at hi

private theorem cr_same_side_cross_ne (u w z : Plane) (hw : ‖w‖=1) (hz : ‖z‖=1)
    (hwz : w≠z) (hside : 0<cross2 u w*cross2 u z) : cross2 w z≠0 := by
  intro hzero
  rcases unit_cross_zero_eq_or_neg w z hw hz hzero with h | h
  · exact hwz h.symm
  · rw [h,cr_cross_neg_right] at hside
    nlinarith [sq_nonneg (cross2 u w)]

theorem clockwise_ray_comparable (u w z : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1) (hz : ‖z‖=1)
    (huw : u≠w) (huz : u≠z) (hwz : w≠z) :
    ClockwiseRayBetween u w z ∨ ClockwiseRayBetween u z w := by
  rcases lt_trichotomy (cross2 u w) 0 with hwr | hw0 | hwl
  · rcases lt_trichotomy (cross2 u z) 0 with hzr | hz0 | hzl
    · have hne := cr_same_side_cross_ne u w z hw hz hwz (mul_pos_of_neg_of_neg hwr hzr)
      rcases lt_or_gt_of_ne hne with h | h
      · right
        have hswap : 0<cross2 z w := by rw [cr_cross_swap]; linarith
        simpa only [ClockwiseRayBetween,ite_eq_right huz,ite_eq_left hzr] using And.intro hwr hswap
      · left
        simpa only [ClockwiseRayBetween,ite_eq_right huw,ite_eq_left hwr] using And.intro hzr h
    · right
      simpa [ClockwiseRayBetween,huz,hz0] using hwr
    · right
      simpa only [ClockwiseRayBetween,ite_eq_right huz,ite_eq_right (not_lt_of_ge hzl.le),
        ite_eq_right (ne_of_gt hzl)] using Or.inl hwr
  · have hwneg : w= -u :=
      (unit_cross_zero_eq_or_neg u w hu hw hw0).resolve_left (fun h => huw h.symm)
    rcases lt_trichotomy (cross2 u z) 0 with hzr | hz0 | hzl
    · left
      simpa [ClockwiseRayBetween,huw,hw0] using hzr
    · have hzneg : z= -u :=
        (unit_cross_zero_eq_or_neg u z hu hz hz0).resolve_left (fun h => huz h.symm)
      exact False.elim (hwz (hwneg.trans hzneg.symm))
    · right
      have hzw : 0<cross2 z w := by
        have heq : cross2 z w=cross2 u z := by rw [hwneg,cr_cross_neg_right,cr_cross_swap]; ring
        rw [heq]
        exact hzl
      simpa only [ClockwiseRayBetween,ite_eq_right huz,ite_eq_right (not_lt_of_ge hzl.le),
        ite_eq_right (ne_of_gt hzl)] using Or.inr hzw
  · rcases lt_trichotomy (cross2 u z) 0 with hzr | hz0 | hzl
    · left
      simpa only [ClockwiseRayBetween,ite_eq_right huw,ite_eq_right (not_lt_of_ge hwl.le),
        ite_eq_right (ne_of_gt hwl)] using Or.inl hzr
    · left
      have hzneg : z= -u :=
        (unit_cross_zero_eq_or_neg u z hu hz hz0).resolve_left (fun h => huz h.symm)
      have hwz' : 0<cross2 w z := by
        have heq : cross2 w z=cross2 u w := by rw [hzneg,cr_cross_neg_right,cr_cross_swap]; ring
        rw [heq]
        exact hwl
      simpa only [ClockwiseRayBetween,ite_eq_right huw,ite_eq_right (not_lt_of_ge hwl.le),
        ite_eq_right (ne_of_gt hwl)] using Or.inr hwz'
    · have hne := cr_same_side_cross_ne u w z hw hz hwz (mul_pos hwl hzl)
      rcases lt_or_gt_of_ne hne with h | h
      · right
        have hswap : 0<cross2 z w := by rw [cr_cross_swap]; linarith
        simpa only [ClockwiseRayBetween,ite_eq_right huz,ite_eq_right (not_lt_of_ge hzl.le),
          ite_eq_right (ne_of_gt hzl)] using Or.inr hswap
      · left
        simpa only [ClockwiseRayBetween,ite_eq_right huw,ite_eq_right (not_lt_of_ge hwl.le),
          ite_eq_right (ne_of_gt hwl)] using Or.inr h

def rayMirror (x : Plane) : Plane :=
  EuclideanSpace.single 0 (x 0)+EuclideanSpace.single 1 (-x 1)

theorem rayMirror_norm (x : Plane) : ‖rayMirror x‖=‖x‖ := by
  have hs : ‖rayMirror x‖^2=‖x‖^2 := by
    simp [rayMirror,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  nlinarith [norm_nonneg (rayMirror x),norm_nonneg x]

theorem rayMirror_injective : Function.Injective rayMirror := by
  intro x y h
  ext i
  fin_cases i
  · have h0 := congrArg (fun z : Plane => z 0) h
    simpa [rayMirror] using h0
  · have h1 := congrArg (fun z : Plane => z 1) h
    have hn : -(x 1)= -(y 1) := by simpa [rayMirror] using h1
    exact neg_injective hn

@[simp] theorem rayMirror_cross (u w : Plane) : cross2 (rayMirror u) (rayMirror w)= -cross2 u w := by
  simp [rayMirror,cross2]
  ring

theorem clockwise_ray_mirror_reverse (u w x : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1) :
    ClockwiseRayBetween (rayMirror w) (rayMirror u) (rayMirror x) ↔ ClockwiseRayBetween u w x := by
  by_cases heq : u=w
  · subst w
    simp [ClockwiseRayBetween,rayMirror_injective.eq_iff]
  have hmirrorNe : rayMirror w≠rayMirror u :=
    fun h => heq (rayMirror_injective h).symm
  have hcross : cross2 (rayMirror w) (rayMirror u)=cross2 u w := by
    rw [rayMirror_cross,cr_cross_swap]
    ring
  rcases lt_trichotomy (cross2 u w) 0 with hneg | hzero | hpos
  · simp only [ClockwiseRayBetween,ite_eq_right hmirrorNe,ite_eq_right heq,hcross,ite_eq_left hneg,
      rayMirror_cross,neg_lt_zero,neg_pos]
    exact and_comm
  · have hwneg : w= -u :=
      (unit_cross_zero_eq_or_neg u w hu hw hzero).resolve_left (fun h => heq h.symm)
    simp only [ClockwiseRayBetween,ite_eq_right hmirrorNe,ite_eq_right heq,hcross,hzero,lt_self_iff_false,
      ite_false,ite_true,rayMirror_cross,neg_lt_zero]
    rw [hwneg,cross2_neg_left]
    exact neg_pos
  · simp only [ClockwiseRayBetween,ite_eq_right hmirrorNe,ite_eq_right heq,hcross,
      ite_eq_right (not_lt_of_ge hpos.le),ite_eq_right (ne_of_gt hpos),rayMirror_cross,neg_lt_zero,neg_pos]
    exact or_comm

theorem empty_clockwise_ray_unique {T : Type*} (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (hinj : Function.Injective direction)
    (a b c : T) (hb : ∀ d, ¬ClockwiseRayBetween (direction a) (direction b) (direction d))
    (hc : ∀ d, ¬ClockwiseRayBetween (direction a) (direction c) (direction d)) : b=c := by
  by_contra hbc
  by_cases hab : a=b
  · subst b
    apply hb c
    simpa [ClockwiseRayBetween] using
      (show direction c≠direction a from fun h => hbc (hinj h).symm)
  by_cases hac : a=c
  · subst c
    apply hc b
    simpa [ClockwiseRayBetween] using
      (show direction b≠direction a from fun h => hab (hinj h).symm)
  have huv : direction a≠direction b := fun h => hab (hinj h)
  have huw : direction a≠direction c := fun h => hac (hinj h)
  have hvw : direction b≠direction c := fun h => hbc (hinj h)
  rcases clockwise_ray_comparable _ _ _ (hunit a) (hunit b) (hunit c) huv huw hvw with h | h
  · exact hb c h
  · exact hc b h

private theorem ray_projective_gap {T : Type*} [Fintype T] (direction : T → Plane)
    (u : Plane) (hu : ‖u‖=1) (hex : ∃ b, cross2 u (direction b)<0) :
    ∃ b, cross2 u (direction b)<0 ∧ ∀ c,
      ¬ (cross2 u (direction c)<0 ∧ 0<cross2 (direction b) (direction c)) := by
  let N := Finset.univ.filter (fun c : T => cross2 u (direction c)<0)
  have hN : N.Nonempty := by
    obtain ⟨b,hb⟩ := hex
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩
  let slope (c : T) := inner ℝ u (direction c)/(-cross2 u (direction c))
  obtain ⟨b,hb,hmax⟩ := N.exists_max_image slope hN
  have hb' := (Finset.mem_filter.mp hb).2
  refine ⟨b,hb',?_⟩
  intro c hc
  have hcN : c∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc.1⟩
  have hbound := hmax c hcN
  have hid := cross2_in_unit_frame u (direction b) (direction c) hu
  have hlt : slope b<slope c := by
    apply (div_lt_div_iff₀ (neg_pos.mpr hb') (neg_pos.mpr hc.1)).mpr
    nlinarith [hc.2]
  exact (not_lt_of_ge hbound) hlt

theorem exists_empty_clockwise_ray {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (a : T) :
    ∃ b, ∀ c, ¬ClockwiseRayBetween (direction a) (direction b) (direction c) := by
  let u := direction a
  have hu : ‖u‖=1 := hunit a
  by_cases hright : ∃ b, cross2 u (direction b)<0
  · obtain ⟨b,hb,hgap⟩ := ray_projective_gap direction u hu hright
    have hne : u≠direction b := by
      intro h
      rw [← h,cross2_self] at hb
      linarith
    refine ⟨b,?_⟩
    intro c
    change ¬ClockwiseRayBetween u (direction b) (direction c)
    simpa only [ClockwiseRayBetween,ite_eq_right hne,ite_eq_left hb] using hgap c
  have hnoRight (c) : ¬ cross2 u (direction c)<0 := fun h => hright ⟨c,h⟩
  by_cases hanti : ∃ b, direction b= -u
  · obtain ⟨b,hb⟩ := hanti
    have hne : u≠direction b := by rw [hb]; exact cr_unit_ne_neg u hu
    have hcross : cross2 u (direction b)=0 := by rw [hb,cr_cross_neg_right,cross2_self,neg_zero]
    refine ⟨b,?_⟩
    intro c
    change ¬ClockwiseRayBetween u (direction b) (direction c)
    simpa [ClockwiseRayBetween,hne,hcross] using hnoRight c
  by_cases hleft : ∃ b, 0<cross2 u (direction b)
  · have hex : ∃ b, cross2 (-u) (direction b)<0 := by
      obtain ⟨b,hb⟩ := hleft
      exact ⟨b,by rw [cross2_neg_left]; linarith⟩
    obtain ⟨b,hb,hgap⟩ := ray_projective_gap direction (-u) (by simpa using hu) hex
    have hbpos : 0<cross2 u (direction b) := by rw [cross2_neg_left] at hb; linarith
    have hne : u≠direction b := by
      intro h
      rw [← h,cross2_self] at hbpos
      linarith
    have hnoLeft (c) : ¬ 0<cross2 (direction b) (direction c) := by
      intro hbc
      have huc : 0≤cross2 u (direction c) := le_of_not_gt (hnoRight c)
      rcases eq_or_lt_of_le huc with hzero | hpos
      · rcases unit_cross_zero_eq_or_neg u (direction c) hu (hunit c) hzero.symm with hsame | hopp
        · rw [hsame,cr_cross_swap] at hbc
          linarith
        · exact hanti ⟨c,hopp⟩
      · exact hgap c ⟨by rw [cross2_neg_left]; linarith,hbc⟩
    refine ⟨b,?_⟩
    intro c
    change ¬ClockwiseRayBetween u (direction b) (direction c)
    simpa only [ClockwiseRayBetween,ite_eq_right hne,ite_eq_right (not_lt_of_ge hbpos.le),
      ite_eq_right (ne_of_gt hbpos)] using not_or.mpr ⟨hnoRight c,hnoLeft c⟩
  · have hall (c) : direction c=u := by
      have hzero : cross2 u (direction c)=0 :=
        le_antisymm (le_of_not_gt (fun h => hleft ⟨c,h⟩)) (le_of_not_gt (hnoRight c))
      exact (unit_cross_zero_eq_or_neg u (direction c) hu (hunit c) hzero).resolve_right
        (fun h => hanti ⟨c,h⟩)
    refine ⟨a,?_⟩
    intro c
    simp only [ClockwiseRayBetween,ite_true]
    exact not_not.mpr (hall c)

def clockwiseRayNext {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (a : T) : T :=
  Classical.choose (exists_empty_clockwise_ray direction hunit a)

theorem clockwiseRayNext_empty {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (a c : T) :
    ¬ClockwiseRayBetween (direction a) (direction (clockwiseRayNext direction hunit a)) (direction c) :=
  Classical.choose_spec (exists_empty_clockwise_ray direction hunit a) c

theorem clockwiseRayNext_injective {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (hinj : Function.Injective direction) :
    Function.Injective (clockwiseRayNext direction hunit) := by
  intro a b hab
  have hmirrorUnit (c : T) : ‖rayMirror (direction c)‖=1 := by rw [rayMirror_norm,hunit c]
  have hmira (c : T) : ¬ClockwiseRayBetween
      (rayMirror (direction (clockwiseRayNext direction hunit a))) (rayMirror (direction a))
        (rayMirror (direction c)) := by
    intro h
    exact clockwiseRayNext_empty direction hunit a c
      ((clockwise_ray_mirror_reverse _ _ _ (hunit a) (hunit _)).mp h)
  have hmirb (c : T) : ¬ClockwiseRayBetween
      (rayMirror (direction (clockwiseRayNext direction hunit a))) (rayMirror (direction b))
        (rayMirror (direction c)) := by
    rw [hab]
    intro h
    exact clockwiseRayNext_empty direction hunit b c
      ((clockwise_ray_mirror_reverse _ _ _ (hunit b) (hunit _)).mp h)
  exact empty_clockwise_ray_unique (fun c => rayMirror (direction c)) hmirrorUnit
    (rayMirror_injective.comp hinj) _ a b hmira hmirb

def clockwiseRayPermutation {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (hinj : Function.Injective direction) : Equiv.Perm T :=
  Equiv.ofBijective (clockwiseRayNext direction hunit)
    ⟨clockwiseRayNext_injective direction hunit hinj,
      Finite.surjective_of_injective (clockwiseRayNext_injective direction hunit hinj)⟩

theorem clockwiseRayPermutation_empty {T : Type*} [Fintype T] (direction : T → Plane)
    (hunit : ∀ a, ‖direction a‖=1) (hinj : Function.Injective direction) (a c : T) :
    ¬ClockwiseRayBetween (direction a) (direction (clockwiseRayPermutation direction hunit hinj a))
      (direction c) := clockwiseRayNext_empty direction hunit a c

end Swanepoel
