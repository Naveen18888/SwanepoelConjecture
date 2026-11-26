module
public import Swanepoel.Combinatorics
public import Swanepoel.CutArithmetic
public import Swanepoel.FacePortLowerBound
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem HalfSystem.cut_half_cap_of_high_bank (H : HalfSystem)
    (hbank : H.HighBankBound) (hhigh : 39*H.k≤100*H.d)
    (o others : ℤ) (hothers : others≤o*(H.k-H.d)) :
    H.R+others≤(H.d+o)*(H.k-H.d) := by
  calc
    H.R+others≤H.d*(H.k-H.d)+o*(H.k-H.d) := add_le_add (hbank hhigh) hothers
    _=(H.d+o)*(H.k-H.d) := by ring

theorem cut_cap_from_half_bounds (K s z kL kR dL dR oL oR R RL RR othersL othersR : ℤ)
    (hk : kL+kR=K+z) (hd : dL+dR=s+z)
    (hoL : dL+oL=s) (hoR : dR+oR=s)
    (hallocation : R≤(RL+othersL)+(RR+othersR))
    (hL : RL+othersL≤(dL+oL)*(kL-dL))
    (hR : RR+othersR≤(dR+oR)*(kR-dR)) : R≤s*(K-s) := by
  calc
    R≤(RL+othersL)+(RR+othersR) := hallocation
    _≤(dL+oL)*(kL-dL)+(dR+oR)*(kR-dR) := add_le_add hL hR
    _=s*(K-s) := cut_product_identity K s z kL kR dL dR oL oR hk hd hoL hoR

def TrackSystem.HighCrossingCap (D : TrackSystem) : Prop :=
  ∀ u ∈ D.ordinary, 61*D.K<100*(D.s u : ℤ) →
    (D.r : ℤ)+D.defects≤(D.s u : ℤ)*(D.K-D.s u)

theorem TrackSystem.family_bound_of_high_crossing_cap (D : TrackSystem)
    (hK : 0≤D.K) (hq : D.QuadraticBound) (hcut : D.HighCrossingCap)
    (A : Finset D.Track) (hA : A⊆D.ordinary) :
    (D.r : ℤ)+D.defects+(∑ u ∈ A, (D.s u : ℤ))≤N (D.K+A.card) := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image A D.s hne
    have hmaxi : ∀ v ∈ A, (D.s v : ℤ)≤D.s u := by
      intro v hv
      exact_mod_cast hmax v hv
    by_cases hlow : 100*(D.s u : ℤ)≤61*D.K
    · exact D.lemma_3_2 hq A (D.s u) hlow hmaxi
    · have hcap := hcut u (hA hu) (by omega)
      have hsum : (∑ v ∈ A, (D.s v : ℤ))≤(A.card : ℤ)*D.s u := by
        calc
          _ ≤ ∑ _v ∈ A, (D.s u : ℤ) := Finset.sum_le_sum hmaxi
          _ = _ := by simp
      exact disjoint_bound_from_cut D.K A.card (D.s u)
        ((D.r : ℤ)+D.defects) (∑ v ∈ A, (D.s v : ℤ)) hcap hsum
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    apply D.lemma_3_2 hq A 0 (by omega)
    simp only [he,Finset.notMem_empty,IsEmpty.forall_iff,implies_true]

theorem TrackSystem.disjoint_bound_of_high_crossing_cap (D : TrackSystem)
    (hK : 0≤D.K) (hq : D.QuadraticBound) (hcut : D.HighCrossingCap) :
    D.DisjointBound := by
  intro A hA _
  exact D.family_bound_of_high_crossing_cap hK hq hcut A hA

theorem PennyGraph.canonical_disjoint_bound_of_high_crossing_cap {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree)
    (hq : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound)
    (hcut : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).HighCrossingCap) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound :=
  TrackSystem.disjoint_bound_of_high_crossing_cap _
    (G.canonical_componentSystem_K_nonneg ht) hq hcut

end Swanepoel
