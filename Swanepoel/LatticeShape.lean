module
public import Swanepoel.Lattice
@[expose] public section

noncomputable section
namespace Swanepoel

def east (p : LatticeSite) : LatticeSite := (p.1+1, p.2)
def north (p : LatticeSite) : LatticeSite := (p.1, p.2+1)

def gridShape (w h r : ℕ) : Finset LatticeSite :=
  (Finset.range w ×ˢ Finset.range h) ∪ (Finset.range r ×ˢ {h})

theorem gridShape_card (w h r : ℕ) : (gridShape w h r).card = w*h+r := by
  have hd : Disjoint (Finset.range w ×ˢ Finset.range h)
      (Finset.range r ×ˢ ({h} : Finset ℕ)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hp hq
    omega
  unfold gridShape
  rw [Finset.card_union_of_disjoint hd]
  simp

theorem gridShape_east (w h r : ℕ) (hr : r ≤ w) :
    (gridShape w h r).filter (fun p => east p ∈ gridShape w h r) =
      gridShape (w-1) h (r-1) := by
  ext ⟨x,y⟩
  simp only [gridShape, east, Finset.mem_filter, Finset.mem_union,
    Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  omega

theorem gridShape_north (w h r : ℕ) (hh : 1 ≤ h) (hr : r ≤ w) :
    (gridShape w h r).filter (fun p => north p ∈ gridShape w h r) =
      gridShape w (h-1) r := by
  ext ⟨x,y⟩
  simp only [gridShape, north, Finset.mem_filter, Finset.mem_union,
    Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  omega

end Swanepoel
