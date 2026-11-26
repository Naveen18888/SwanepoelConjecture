module
public import Swanepoel.RhombusTransitions
@[expose] public section

noncomputable section
namespace Swanepoel

theorem TrackSystem.total_track_count (D : TrackSystem) : D.p+D.t=D.count := by
  simpa only [TrackSystem.p,TrackSystem.t,TrackSystem.terminal,Finset.card_univ,
    Fintype.card_fin] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D.ordinary)

theorem TrackSystem.effective_count (D : TrackSystem) :
    D.K+D.t=(D.count : ℤ)-2*D.defects := by
  have h : (D.p : ℤ)+D.t=D.count := by exact_mod_cast D.total_track_count
  unfold TrackSystem.K
  omega

theorem componentSystem_effective_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (ordinary : Finset (TrackComponent G)) (defects : ℕ) :
    (componentSystem G ht ordinary defects).K+(componentSystem G ht ordinary defects).t=
      (Fintype.card (TrackComponent G) : ℤ)-2*defects :=
  TrackSystem.effective_count (componentSystem G ht ordinary defects)

def geometricBlockCounts {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) (f : ℕ)
    (heuler : (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+f)=1)
    (heffective : 0≤(Fintype.card (TrackComponent G) : ℤ)-2*f) : BlockCounts where
  n := n
  m := G.edgeCount
  q := Fintype.card (RhombusSet G)
  f := f
  T := Fintype.card (TrackComponent G)
  x := (Fintype.card (TrackComponent G) : ℤ)-2*f
  tracks := geometric_track_identity G ht
  euler := heuler
  effective := rfl
  effective_nonneg := heffective

end Swanepoel
