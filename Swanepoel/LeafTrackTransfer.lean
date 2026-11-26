module
public import Swanepoel.L38BankCrossingRealization
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem N_mono_nonneg {x y : ℤ} (hx : 0≤x) (hxy : x≤y) : N x≤N y := by
  have hsq : x^2≤y^2 := by nlinarith
  unfold N
  omega

namespace TrackSystem

structure IsolatedDeletion (D E : TrackSystem) where
  leaf : D.Track
  map : E.Track→D.Track
  injective : Function.Injective map
  image_univ : (Finset.univ.image map)=Finset.univ.erase leaf
  crossing : ∀ u v,E.crossing.Adj u v↔D.crossing.Adj (map u) (map v)
  terminal : ∀ u,u∈E.terminal↔map u∈D.terminal
  defects : E.defects=D.defects
  isolated : ∀ v,¬D.crossing.Adj leaf v

namespace IsolatedDeletion
variable {D E : TrackSystem} (R : IsolatedDeletion D E)
include R

theorem map_ne_leaf (u : E.Track) : R.map u≠R.leaf := by
  have h : R.map u∈Finset.univ.image R.map :=
    Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
  rw [R.image_univ] at h
  exact (Finset.mem_erase.mp h).1

theorem ordinary_iff (u : E.Track) : u∈E.ordinary↔R.map u∈D.ordinary := by
  have h := not_congr (R.terminal u)
  simpa only [TrackSystem.terminal,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using h

def pullback (A : Finset D.Track) : Finset E.Track :=
  Finset.univ.filter (fun u => R.map u∈A)

theorem pullback_image (A : Finset D.Track) :
    (R.pullback A).image R.map=A.erase R.leaf := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨R.map_ne_leaf u,(Finset.mem_filter.mp hu).2⟩
  · intro hv
    have h := Finset.mem_erase.mp hv
    have hm : v∈Finset.univ.image R.map := by
      rw [R.image_univ]
      exact Finset.mem_erase.mpr ⟨h.1,Finset.mem_univ _⟩
    obtain ⟨u,_hu,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩,rfl⟩

theorem pullback_card_le (A : Finset D.Track) : (R.pullback A).card≤A.card := by
  calc
    _=((R.pullback A).image R.map).card :=
      (Finset.card_image_of_injective _ R.injective).symm
    _=(A.erase R.leaf).card := congrArg Finset.card (R.pullback_image A)
    _≤A.card := Finset.card_le_card (Finset.erase_subset _ _)

theorem pullback_ordinary (A : Finset D.Track) (hA : A⊆D.ordinary) :
    R.pullback A⊆E.ordinary := by
  intro u hu
  exact (R.ordinary_iff u).mpr (hA (Finset.mem_filter.mp hu).2)

theorem pullback_disjoint (A : Finset D.Track) (hA : D.Disjoint A) :
    E.Disjoint (R.pullback A) := by
  intro u hu v hv huv
  exact hA (R.map u) (Finset.mem_filter.mp hu).2
    (R.map v) (Finset.mem_filter.mp hv).2 ((R.crossing u v).mp huv)

theorem terminal_image : E.terminal.image R.map=D.terminal.erase R.leaf := by
  have heq : R.pullback D.terminal=E.terminal := by
    ext u
    simp only [pullback,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (R.terminal u).symm
  rw [← heq,R.pullback_image]

theorem internal_erase (A : Finset D.Track) : D.internal (A.erase R.leaf)=D.internal A := by
  by_cases hl : R.leaf∈A
  · have hfilter : (A.erase R.leaf).filter (D.crossing.Adj R.leaf)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v _
      exact R.isolated v
    have h := D.internal_insert (A.erase R.leaf) R.leaf (by simp)
    rw [Finset.insert_erase hl,hfilter,Finset.card_empty,add_zero] at h
    exact h.symm
  · rw [Finset.erase_eq_of_notMem hl]

theorem r_eq : E.r=D.r := by
  have h := E.internal_image_of_injOn D E.terminal R.map R.injective.injOn
    (fun u _ v _ => (R.crossing u v).symm)
  rw [R.terminal_image] at h
  change E.internal E.terminal=D.internal D.terminal
  exact h.symm.trans (R.internal_erase D.terminal)

theorem s_leaf : D.s R.leaf=0 := by
  have hfilter : D.terminal.filter (D.crossing.Adj R.leaf)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v _
    exact R.isolated v
  change (D.terminal.filter (D.crossing.Adj R.leaf)).card=0
  simp only [hfilter,Finset.card_empty]

theorem s_map (u : E.Track) : E.s u=D.s (R.map u) := by
  have hfilter : (E.terminal.filter (E.crossing.Adj u)).image R.map=
      D.terminal.filter (D.crossing.Adj (R.map u)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      have h := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨(R.terminal w).mp h.1,(R.crossing u w).mp h.2⟩
    · intro hv
      have h := Finset.mem_filter.mp hv
      have hne : v≠R.leaf := by
        intro heq
        rw [heq] at h
        exact R.isolated (R.map u) (D.crossing.adj_symm h.2)
      have hm : v∈Finset.univ.image R.map := by
        rw [R.image_univ]
        exact Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩
      obtain ⟨w,_hw,rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
        ⟨(R.terminal w).mpr h.1,(R.crossing u w).mpr h.2⟩,rfl⟩
  have hcard := congrArg Finset.card hfilter
  rw [Finset.card_image_of_injective _ R.injective] at hcard
  exact hcard

theorem K_le : E.K≤D.K := by
  have hp : E.p≤D.p := by
    change E.terminal.card≤D.terminal.card
    rw [← Finset.card_image_of_injective E.terminal R.injective,R.terminal_image]
    exact Finset.card_le_card (Finset.erase_subset _ _)
  unfold TrackSystem.K
  rw [R.defects]
  omega

theorem selected_sum_eq (A : Finset D.Track) :
    (∑ u∈R.pullback A,(E.s u : ℤ))=∑ v∈A,(D.s v : ℤ) := by
  calc
    _=∑ u∈R.pullback A,(D.s (R.map u) : ℤ) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [R.s_map]
    _=∑ v∈(R.pullback A).image R.map,(D.s v : ℤ) := by
      rw [Finset.sum_image (fun _ _ _ _ h => R.injective h)]
    _=∑ v∈A.erase R.leaf,(D.s v : ℤ) := by rw [R.pullback_image]
    _=∑ v∈A,(D.s v : ℤ) := by
      by_cases hl : R.leaf∈A
      · have h := Finset.sum_erase_add (s := A) (fun v => (D.s v : ℤ)) hl
        rw [R.s_leaf] at h
        simpa only [Nat.cast_zero,add_zero] using h
      · rw [Finset.erase_eq_of_notMem hl]

theorem disjointBound (hK : 0≤E.K) (hrec : E.DisjointBound) : D.DisjointBound := by
  intro A hA hdisj
  have h := hrec (R.pullback A) (R.pullback_ordinary A hA) (R.pullback_disjoint A hdisj)
  rw [R.r_eq,R.defects,R.selected_sum_eq] at h
  have hcard : ((R.pullback A).card : ℤ)≤A.card := by
    exact_mod_cast R.pullback_card_le A
  have hbudget0 : 0≤E.K+(R.pullback A).card := by positivity
  have hbudget : E.K+(R.pullback A).card≤D.K+A.card := by
    have hk := R.K_le
    omega
  exact h.trans (N_mono_nonneg hbudget0 hbudget)

end IsolatedDeletion

theorem disjointBound_of_erase_isolated (D E : TrackSystem) (l : D.Track)
    (f : E.Track→D.Track) (hf : Function.Injective f)
    (himage : Finset.univ.image f=Finset.univ.erase l)
    (hcross : ∀ u v,E.crossing.Adj u v↔D.crossing.Adj (f u) (f v))
    (hterminal : ∀ u,u∈E.terminal↔f u∈D.terminal)
    (hdefects : E.defects=D.defects) (hisolated : ∀ v,¬D.crossing.Adj l v)
    (hK : 0≤E.K) (hrec : E.DisjointBound) : D.DisjointBound :=
  (IsolatedDeletion.mk l f hf himage hcross hterminal hdefects hisolated).disjointBound hK hrec

end TrackSystem
end Swanepoel
