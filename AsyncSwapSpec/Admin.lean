import AsyncSwapSpec.Order

/-!
# Ownership and signed-action nonces

Models the admin surface of `AsyncSwap.sol`: two-step ownership
(`transferOwnership` / `acceptOwnership`) and the unordered-nonce registry consumed by
`_verify` and `invalidateNonce`.
-/

namespace AsyncSwap

structure Admin where
  owner : Address
  pendingOwner : Address
  nonceUsed : Address → ℕ → Bool

inductive AdminAction where
  | transferOwnership (sender newOwner : Address)
  | acceptOwnership (sender : Address)
  | invalidateNonce (sender : Address) (nonce : ℕ)
  /-- `_verify` for a signed maker action: burns the nonce before checking the signature. -/
  | verify (maker : Address) (nonce : ℕ) (deadline now : ℕ)
  /-- Any non-admin call (swap, fill, cancel, …): touches neither ownership nor nonces. -/
  | other

namespace Admin

def step (s : Admin) : AdminAction → Option Admin
  | .transferOwnership sender newOwner =>
      if sender ≠ s.owner then none
      else if newOwner = 0 then none
      else some { s with pendingOwner := newOwner }
  | .acceptOwnership sender =>
      if sender ≠ s.pendingOwner then none
      else some { s with owner := sender, pendingOwner := 0 }
  | .invalidateNonce sender nonce =>
      if s.nonceUsed sender nonce then none
      else some { s with nonceUsed := fun a n => if a = sender ∧ n = nonce then true else s.nonceUsed a n }
  | .verify maker nonce deadline now =>
      if deadline < now then none
      else if s.nonceUsed maker nonce then none
      else some { s with nonceUsed := fun a n => if a = maker ∧ n = nonce then true else s.nonceUsed a n }
  | .other => some s

/-- `owner` changes only through `acceptOwnership`, and only to the nominated `pendingOwner`
    (Certora rule `ownerChangeOnlyViaAcceptOwnership`, now a theorem). -/
theorem owner_change_only_via_accept {s s' : Admin} {a : AdminAction}
    (h : s.step a = some s') (hne : s'.owner ≠ s.owner) :
    a = .acceptOwnership s.pendingOwner ∧ s'.owner = s.pendingOwner := by
  cases a <;> simp only [step] at h <;> (try split_ifs at h) <;> simp only [Option.some.injEq] at h
    <;> subst h <;> simp_all

/-- Only the current owner can nominate, and never the zero address. -/
theorem transfer_requires_owner {s s' : Admin} {sender newOwner : Address}
    (h : s.step (.transferOwnership sender newOwner) = some s') :
    sender = s.owner ∧ newOwner ≠ 0 := by
  simp only [step] at h; split_ifs at h with h1 h2
  exact ⟨by simpa using h1, h2⟩

/-- Nominating does not transfer control. -/
theorem transfer_keeps_owner {s s' : Admin} {sender newOwner : Address}
    (h : s.step (.transferOwnership sender newOwner) = some s') : s'.owner = s.owner := by
  simp only [step] at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- Accepting clears the nomination, so it cannot be replayed. -/
theorem accept_clears_pending {s s' : Admin} {sender : Address}
    (h : s.step (.acceptOwnership sender) = some s') : s'.pendingOwner = 0 := by
  simp only [step] at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- A consumed nonce stays consumed forever (no replay of signed actions). -/
theorem nonce_monotone {s s' : Admin} {a : AdminAction} (h : s.step a = some s')
    {maker : Address} {nonce : ℕ} (hused : s.nonceUsed maker nonce = true) :
    s'.nonceUsed maker nonce = true := by
  cases a <;> simp only [step] at h <;> (try split_ifs at h) <;> simp only [Option.some.injEq] at h
    <;> subst h <;> simp_all

/-- A signed action cannot be verified twice with the same nonce. -/
theorem verify_no_replay {s s' : Admin} {maker nonce deadline now : ℕ}
    (h : s.step (.verify maker nonce deadline now) = some s') :
    ∀ deadline' now' s'', s'.step (.verify maker nonce deadline' now') ≠ some s'' := by
  intro d n s'' h'
  simp only [step] at h h'
  split_ifs at h with h1 h2
  simp only [Option.some.injEq] at h; subst h
  split_ifs at h' with h3 h4
  simp at h4

/-- An expired signature is rejected before the nonce is touched. -/
theorem verify_respects_deadline {s s' : Admin} {maker nonce deadline now : ℕ}
    (h : s.step (.verify maker nonce deadline now) = some s') : now ≤ deadline := by
  simp only [step] at h; split_ifs at h with h1; omega

end Admin
end AsyncSwap
