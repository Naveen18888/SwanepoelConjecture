module
public import Swanepoel.HalfOpenAntipodalCover
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def angular120Slots (s t θ : ℝ) : ℕ :=
  (if θ∈Set.Ioc s (s+2) then 1 else 0)+(if θ∈Set.Ioc t (t+2) then 1 else 0)

def pentagonSingleAngles (g θ : ℝ) : Prop :=
  θ∈Set.Ioo (1:ℝ) 2 ∨ θ∈Set.Ioo (4-g) (5-g)

def pentagonDoubleAngles (a b g θ : ℝ) : Prop :=
  θ∈Set.Ioo (1+a) 2 ∨ θ∈Set.Ioo (4-g) (5-g-b)

theorem angular120Slots_one_of_union {s t θ : ℝ}
    (h : θ∈Set.Ioc s (s+2) ∨ θ∈Set.Ioc t (t+2)) :
    1≤angular120Slots s t θ := by
  unfold angular120Slots
  split_ifs <;> simp_all

theorem angular120Slots_two_of_inter {s t θ : ℝ}
    (h : θ∈Set.Ioc s (s+2) ∧ θ∈Set.Ioc t (t+2)) :
    2≤angular120Slots s t θ := by
  simp only [angular120Slots,ite_eq_left h.1,ite_eq_left h.2]
  norm_num

theorem angular120Slots_one_of_range {s d θ : ℝ} (_hd0 : 0≤d) (hd2 : d≤2)
    (hθ : s<θ ∧ θ<s+d+2) : 1≤angular120Slots s (s+d) θ := by
  apply angular120Slots_one_of_union
  by_cases h : θ≤s+2
  · exact Or.inl ⟨hθ.1,h⟩
  · exact Or.inr ⟨by linarith,by linarith [hθ.2]⟩

theorem pentagon_angular_intervals_cover (a b g : ℝ)
    (ha0 : 0<a) (_ha2 : a<2) (hb0 : 0<b) (_hb2 : b<2)
    (hg0 : 0<g) (hg2 : g<2) (hag : 2≤a+g) (hbg : 2≤b+g)
    (habg : 3≤a+b+g) :
    ∃ s t : ℝ,(t-s=1 ∨ t-s=2) ∧
      (∀ θ,pentagonSingleAngles g θ → 1≤angular120Slots s t θ) ∧
      (∀ θ,pentagonDoubleAngles a b g θ → 2≤angular120Slots s t θ) := by
  by_cases ha : 1≤a
  · by_cases hb : 1≤b
    · refine ⟨1,3,Or.inr (by norm_num),?_,?_⟩
      · intro θ hθ
        have hθ' : (1:ℝ)<θ ∧ θ<1+2+2 := by
          rcases hθ with hθ | hθ <;> constructor <;> linarith [hθ.1,hθ.2]
        simpa only [show (1:ℝ)+2=3 by norm_num] using
          angular120Slots_one_of_range (d := 2) (by norm_num) (by norm_num) hθ'
      · intro θ hθ
        rcases hθ with hθ | hθ <;> exfalso <;> linarith [hθ.1,hθ.2]
    · have hb1 : b<1 := lt_of_not_ge hb
      let s := 3-g-b
      refine ⟨s,s+1,Or.inl (by ring),?_,?_⟩
      · intro θ hθ
        apply angular120Slots_one_of_range (d := 1) (by norm_num) (by norm_num)
        dsimp [s]
        rcases hθ with hθ | hθ <;> constructor <;> linarith [hθ.1,hθ.2]
      · intro θ hθ
        apply angular120Slots_two_of_inter
        dsimp [s]
        rcases hθ with hθ | hθ <;> constructor <;> constructor <;> linarith [hθ.1,hθ.2]
  · have ha1 : a<1 := lt_of_not_ge ha
    refine ⟨a,a+1,Or.inl (by ring),?_,?_⟩
    · intro θ hθ
      apply angular120Slots_one_of_range (d := 1) (by norm_num) (by norm_num)
      rcases hθ with hθ | hθ <;> constructor <;> linarith [hθ.1,hθ.2]
    · intro θ hθ
      apply angular120Slots_two_of_inter
      rcases hθ with hθ | hθ <;> constructor <;> constructor <;> linarith [hθ.1,hθ.2]

theorem pentagon_angular_multiplicity_bound (a b g : ℝ)
    (ha0 : 0<a) (ha2 : a<2) (hb0 : 0<b) (hb2 : b<2)
    (hg0 : 0<g) (hg2 : g<2) (hag : 2≤a+g) (hbg : 2≤b+g)
    (habg : 3≤a+b+g) :
    ∃ s t : ℝ,(t-s=1 ∨ t-s=2) ∧ ∀ (θ : ℝ) (k : ℕ),
      k≤2 → (0<k → pentagonSingleAngles g θ) →
      (k=2 → pentagonDoubleAngles a b g θ) → k≤angular120Slots s t θ := by
  obtain ⟨s,t,hst,hs,hd⟩ := pentagon_angular_intervals_cover a b g ha0 ha2 hb0 hb2 hg0 hg2 hag hbg habg
  refine ⟨s,t,hst,?_⟩
  intro θ k hk hsingle hdouble
  by_cases hk0 : k=0
  · exact hk0 ▸ Nat.zero_le _
  by_cases hk2 : k=2
  · exact hk2 ▸ hd θ (hdouble hk2)
  have hk1 : k=1 := by omega
  exact hk1 ▸ hs θ (hsingle (by omega))

end Swanepoel
