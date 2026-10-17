// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {Currency} from "v4-core/types/Currency.sol";
import {PoolKey} from "v4-core/types/PoolKey.sol";
import {PoolId, PoolIdLibrary} from "v4-core/types/PoolId.sol";
import {StateLibrary} from "v4-core/libraries/StateLibrary.sol";
import {CurrencySettler} from "./libraries/CurrencySettler.sol";

/// @notice The hook's PoolManager settlement primitives. Every one of them leaves the hook's own currency
///         deltas where it found them (`V2/Spec.lean` `payOutBody_neutral`, `settleBidBody_neutral`), which is
///         why any unlock branch that composes them nets to zero.
abstract contract HookSettlement {
    using CurrencySettler for Currency;
    using PoolIdLibrary for PoolKey;
    using StateLibrary for IPoolManager;

    IPoolManager public immutable manager;
    /// @notice Receives protocol fees and forfeited bids as ERC-6909 claims.
    address public immutable feeVault;
    /// @notice The quote currency (USDC) every pool must contain. Bids are paid in it, and an order that
    ///         spends it is a buy. It may be either `currency0` or `currency1` of a pool.
    Currency public immutable numeraire;

    error InvalidNumeraire();

    event PriorityFeeDonated(PoolId indexed poolId, uint256 amount);
    event PriorityFeeForfeited(PoolId indexed poolId, uint256 amount);

    constructor(IPoolManager _manager, address _feeVault, Currency _numeraire) {
        // A token, never native: bids are pulled with `transferFrom`.
        if (Currency.unwrap(_numeraire).code.length == 0) revert InvalidNumeraire();
        manager = _manager;
        feeVault = _feeVault;
        numeraire = _numeraire;
    }

    /// @dev `_transferEscrow` (`payOutBody`): burn the hook's escrow claim and pay the recipient — as ERC-6909
    ///      claims when the currency is native (redeemable through `NativeClaims`), as tokens otherwise.
    function _transferEscrow(Currency currency, address recipient, uint256 amount) internal {
        if (amount == 0) return;
        currency.settle(manager, address(this), amount, true);
        currency.take(manager, recipient, amount, currency.isAddressZero());
    }

    /// @dev `settlePriorityFee` (`settleBidBody`): a bid is never refunded. It is donated to the pool's active
    ///      LPs; with no liquidity to receive it, it is forfeited to the vault. Either way the hook's numeraire
    ///      claim is burned.
    function _settlePriorityFee(PoolKey memory key, uint256 amount) internal {
        if (amount == 0) return;
        if (_hasLiquidity(key)) {
            bool numeraireIs0 = key.currency0 == numeraire;
            manager.donate(key, numeraireIs0 ? amount : 0, numeraireIs0 ? 0 : amount, "");
            numeraire.settle(manager, address(this), amount, true);
            emit PriorityFeeDonated(key.toId(), amount);
        } else {
            numeraire.settle(manager, address(this), amount, true);
            numeraire.take(manager, feeVault, amount, true);
            emit PriorityFeeForfeited(key.toId(), amount);
        }
    }

    /// @dev `poolManager.getLiquidity(poolId) != 0`.
    function _hasLiquidity(PoolKey memory key) internal view returns (bool) {
        return manager.getLiquidity(key.toId()) != 0;
    }
}
