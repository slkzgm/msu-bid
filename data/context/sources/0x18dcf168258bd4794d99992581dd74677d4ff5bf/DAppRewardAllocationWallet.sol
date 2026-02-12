

// Sources flattened with hardhat v2.22.6 https://hardhat.org

// SPDX-License-Identifier: MIT

// File @openzeppelin/contracts/utils/Context.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// File @openzeppelin/contracts/metatx/ERC2771Context.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.7.0) (metatx/ERC2771Context.sol)

pragma solidity ^0.8.9;

/**
 * @dev Context variant with ERC2771 support.
 */
abstract contract ERC2771Context is Context {
    /// @custom:oz-upgrades-unsafe-allow state-variable-immutable
    address private immutable _trustedForwarder;

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor(address trustedForwarder) {
        _trustedForwarder = trustedForwarder;
    }

    function isTrustedForwarder(address forwarder) public view virtual returns (bool) {
        return forwarder == _trustedForwarder;
    }

    function _msgSender() internal view virtual override returns (address sender) {
        if (isTrustedForwarder(msg.sender)) {
            // The assembly code is more direct than the Solidity version using `abi.decode`.
            /// @solidity memory-safe-assembly
            assembly {
                sender := shr(96, calldataload(sub(calldatasize(), 20)))
            }
        } else {
            return super._msgSender();
        }
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        if (isTrustedForwarder(msg.sender)) {
            return msg.data[:msg.data.length - 20];
        } else {
            return super._msgData();
        }
    }
}


// File @openzeppelin/contracts/security/Pausable.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}


// File @openzeppelin/contracts/utils/introspection/IERC165.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}


// File @openzeppelin/contracts/token/ERC1155/IERC1155Receiver.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC1155/IERC1155Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @dev _Available since v3.1._
 */
interface IERC1155Receiver is IERC165 {
    /**
     * @dev Handles the receipt of a single ERC1155 token type. This function is
     * called at the end of a `safeTransferFrom` after the balance has been updated.
     *
     * NOTE: To accept the transfer, this must return
     * `bytes4(keccak256("onERC1155Received(address,address,uint256,uint256,bytes)"))`
     * (i.e. 0xf23a6e61, or its own function selector).
     *
     * @param operator The address which initiated the transfer (i.e. msg.sender)
     * @param from The address which previously owned the token
     * @param id The ID of the token being transferred
     * @param value The amount of tokens being transferred
     * @param data Additional data with no specified format
     * @return `bytes4(keccak256("onERC1155Received(address,address,uint256,uint256,bytes)"))` if transfer is allowed
     */
    function onERC1155Received(
        address operator,
        address from,
        uint256 id,
        uint256 value,
        bytes calldata data
    ) external returns (bytes4);

    /**
     * @dev Handles the receipt of a multiple ERC1155 token types. This function
     * is called at the end of a `safeBatchTransferFrom` after the balances have
     * been updated.
     *
     * NOTE: To accept the transfer(s), this must return
     * `bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"))`
     * (i.e. 0xbc197c81, or its own function selector).
     *
     * @param operator The address which initiated the batch transfer (i.e. msg.sender)
     * @param from The address which previously owned the token
     * @param ids An array containing ids of each token being transferred (order and length must match values array)
     * @param values An array containing amounts of each token being transferred (order and length must match ids array)
     * @param data Additional data with no specified format
     * @return `bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"))` if transfer is allowed
     */
    function onERC1155BatchReceived(
        address operator,
        address from,
        uint256[] calldata ids,
        uint256[] calldata values,
        bytes calldata data
    ) external returns (bytes4);
}


// File @openzeppelin/contracts/utils/introspection/ERC165.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165 is IERC165 {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId;
    }
}


// File @openzeppelin/contracts/token/ERC1155/utils/ERC1155Receiver.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC1155/utils/ERC1155Receiver.sol)

pragma solidity ^0.8.0;


/**
 * @dev _Available since v3.1._
 */
abstract contract ERC1155Receiver is ERC165, IERC1155Receiver {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override(ERC165, IERC165) returns (bool) {
        return interfaceId == type(IERC1155Receiver).interfaceId || super.supportsInterface(interfaceId);
    }
}


// File @openzeppelin/contracts/token/ERC1155/utils/ERC1155Holder.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC1155/utils/ERC1155Holder.sol)

pragma solidity ^0.8.0;

/**
 * Simple implementation of `ERC1155Receiver` that will allow a contract to hold ERC1155 tokens.
 *
 * IMPORTANT: When inheriting this contract, you must include a way to use the received tokens, otherwise they will be
 * stuck.
 *
 * @dev _Available since v3.1._
 */
contract ERC1155Holder is ERC1155Receiver {
    function onERC1155Received(
        address,
        address,
        uint256,
        uint256,
        bytes memory
    ) public virtual override returns (bytes4) {
        return this.onERC1155Received.selector;
    }

    function onERC1155BatchReceived(
        address,
        address,
        uint256[] memory,
        uint256[] memory,
        bytes memory
    ) public virtual override returns (bytes4) {
        return this.onERC1155BatchReceived.selector;
    }
}


// File @openzeppelin/contracts/token/ERC20/extensions/draft-IERC20Permit.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}


// File @openzeppelin/contracts/token/ERC20/IERC20.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}


// File @openzeppelin/contracts/utils/Address.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}


// File @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;



/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


// File @openzeppelin/contracts/token/ERC721/IERC721Receiver.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC721/IERC721Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @title ERC721 token receiver interface
 * @dev Interface for any contract that wants to support safeTransfers
 * from ERC721 asset contracts.
 */
interface IERC721Receiver {
    /**
     * @dev Whenever an {IERC721} `tokenId` token is transferred to this contract via {IERC721-safeTransferFrom}
     * by `operator` from `from`, this function is called.
     *
     * It must return its Solidity selector to confirm the token transfer.
     * If any other value is returned or the interface is not implemented by the recipient, the transfer will be reverted.
     *
     * The selector can be obtained in Solidity with `IERC721Receiver.onERC721Received.selector`.
     */
    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4);
}


// File @openzeppelin/contracts/token/ERC721/utils/ERC721Holder.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC721/utils/ERC721Holder.sol)

pragma solidity ^0.8.0;

/**
 * @dev Implementation of the {IERC721Receiver} interface.
 *
 * Accepts all token transfers.
 * Make sure the contract is able to use its token with {IERC721-safeTransferFrom}, {IERC721-approve} or {IERC721-setApprovalForAll}.
 */
contract ERC721Holder is IERC721Receiver {
    /**
     * @dev See {IERC721Receiver-onERC721Received}.
     *
     * Always returns `IERC721Receiver.onERC721Received.selector`.
     */
    function onERC721Received(
        address,
        address,
        uint256,
        bytes memory
    ) public virtual override returns (bytes4) {
        return this.onERC721Received.selector;
    }
}


// File @projecta/util-contracts/access/NextOwnable.sol@v0.7.3

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;


/// @notice Extends Ownable to provide two-level role management functionalities: owner and executors.
contract NextOwnable is Context, Ownable {
    mapping(address => bool) private _isExecutor;

    event ExecutorGranted(address indexed account);
    event ExecutorRevoked(address indexed account);

    modifier onlyAtLeastExecutor() {
        _checkAtLeastExecutor(_msgSender());
        _;
    }

    /// @notice Grant the given address executor role. Only owner can call.
    function grantExecutor(address executor) external virtual onlyOwner {
        _grantExecutor(executor);
    }

    /// @notice Revoke executor role from the given address. Only owner can call.
    function revokeExecutor(address executor) external virtual onlyOwner {
        _revokeExecutor(executor);
    }

    /// @notice Returns true if the given address is an executor.
    function isExecutor(address account) public view virtual returns (bool) {
        return _isExecutor[account];
    }

    /// @notice Returns true if the give address is either the owner or an executor.
    function isAtLeastExecutor(address account) public view virtual returns (bool) {
        return _isExecutor[account] || account == owner();
    }

    /// @notice Grant the given address executor role.
    function _grantExecutor(address executor) internal virtual {
        require(!_isExecutor[executor], "NextOwnable/grantExecutorConflict: account is already an executor");
        _isExecutor[executor] = true;
        emit ExecutorGranted(executor);
    }

    /// @notice Revoke executor role from the given address.
    function _revokeExecutor(address executor) internal virtual {
        require(_isExecutor[executor], "NextOwnable/revokeExecutorConflict: account is already a non-executor");
        _isExecutor[executor] = false;
        emit ExecutorRevoked(executor);
    }

    /// @notice Reverts if the given address is not the owner.
    function _checkOwner(address account) internal view virtual {
        require(owner() == account, "NextOwnable/ownerForbidden: account is not the owner");
    }

    /// @notice Reverts if the given address it neither the owner nor an executor.
    function _checkAtLeastExecutor(address account) internal view virtual {
        require(
            _isExecutor[account] || owner() == account,
            "NextOwnable/executorForbidden: account is neither the owner nor an executor"
        );
    }
}


// File @projecta/util-contracts/access/NextOwnablePausable.sol@v0.7.3

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;



/// @notice Extends NextOwnable and Pausable to provide a useful modifier whenExecutable and pause/unpause function.
contract NextOwnablePausable is Context, NextOwnable, Pausable {
    modifier whenExecutable() {
        _checkExecutable(_msgSender());
        _;
    }

    /// @notice Pauses the contract. Only executor or owner can call.
    function pause() external virtual onlyAtLeastExecutor {
        _pause();
    }

    /// @notice Unpauses the contract. Only owner can call.
    function unpause() external virtual onlyOwner {
        _unpause();
    }

    /// @notice Checks both isAtLeastExecutor and not paused, but the owner can pass even when paused.
    function _checkExecutable(address account) internal view virtual {
        /*
         * Even when paused, owner can pass.
         * There are two cases of rejection:
         * 1. not paused but account is neither an executor nor the owner
         *    reverts because account is not at least executor
         * 2. paused and account is not the owner
         *    reverts because of two reasons: paused, not the owner
         *    revert message says the former, "paused"
         */
        if (paused()) {
            if (owner() != account) _checkNotPaused(); // revert with appropriate message, preceded by a redundant check
            return;
        }
        _checkAtLeastExecutor(account);
    }

    /// @notice Returns true if not paused and the given account is an executor, or the given executor is the owner.
    function _isExecutable(address account) internal view virtual returns (bool) {
        return (!paused() && isExecutor(account)) || owner() == account;
    }

    function _checkNotPaused() internal view virtual whenNotPaused {}

    function _checkPaused() internal view virtual whenPaused {}
}


// File @projecta/util-contracts/exec/interfaces/IExec.sol@v0.7.3

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

interface IExec {
    struct Call {
        address to;
        bytes data;
        uint256 value;
    }

    function exec(address to, bytes memory data, uint256 value) external payable;

    function batchExec(Call[] calldata calls) external payable;
}


// File @projecta/util-contracts/exec/Exec.sol@v0.7.3

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;


/// @notice Provides exec and batchExec function for contracts that behave like a smart contract wallet.
///
/// Although exec and batchExec function is payable and not prohibiting storing the received native
/// tokens, by default, all the received native tokens should be spent before the exec or batchExec returns, and it is
/// caller's responsibility to match the transaction's value and the total amount of native tokens being spent.
///
/// Note that NativeERC20 contract can move this contract's token even if the internal call has zero value.
contract Exec is IExec {
    /// @notice Makes an arbitrary internal transaction with the given to, data and value.
    function exec(address to, bytes memory data, uint256 value) external payable override {
        _beforeExec();
        _exec(to, data, value);
        _afterExec();
    }

    /// @notice Makes arbitrary internal transactions in batch.
    function batchExec(Call[] calldata calls) external payable override {
        _beforeExec();
        for (uint256 i = 0; i < calls.length; i++) {
            Call calldata call = calls[i];
            _exec(call.to, call.data, call.value);
        }
        _afterExec();
    }

    /// @notice Callback function which is called before each internal transaction is made.
    function _beforeEachExec(address to, bytes memory data, uint256 value) internal virtual {}

    /// @notice Callback function which is called after each internal transaction is made.
    function _afterEachExec(address to, bytes memory data, uint256 value) internal virtual {}

    /// @notice Callback function which is called at the beginning of either exec or batchExec.
    function _beforeExec() internal virtual {}

    /// @notice Callback function which is called at the end of either exec or batchExec.
    function _afterExec() internal virtual {}

    /// @notice A low-level function that makes a low-level internal transaction.
    function _exec(address to, bytes memory data, uint256 value) private {
        _beforeEachExec(to, data, value);
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returnData) = to.call{ value: value }(data);
        Address.verifyCallResult(success, returnData, "Exec/noReason: low-level call failed");
        _afterEachExec(to, data, value);
    }
}


// File @openzeppelin/contracts/utils/math/Math.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/Math.sol)

pragma solidity ^0.8.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1);

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator,
        Rounding rounding
    ) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10**64) {
                value /= 10**64;
                result += 64;
            }
            if (value >= 10**32) {
                value /= 10**32;
                result += 32;
            }
            if (value >= 10**16) {
                value /= 10**16;
                result += 16;
            }
            if (value >= 10**8) {
                value /= 10**8;
                result += 8;
            }
            if (value >= 10**4) {
                value /= 10**4;
                result += 4;
            }
            if (value >= 10**2) {
                value /= 10**2;
                result += 2;
            }
            if (value >= 10**1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10**result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result * 8) < value ? 1 : 0);
        }
    }
}


// File contracts/Interfaces/INXPCAmountManager.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;

interface INXPCAmountManager {
    function totalSupply() external view returns (uint256);

    function addBurnedAmount(uint256 amount) external;

    function addMintedAmount(uint256 amount) external;
}


// File contracts/ItemIssuance/ItemIssuance.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;






/// @title ItemIssuance - A contract to issue items
/// @dev Main features
///      - All ERC721 of Nexpace are created through this contract.
///      - Items are periodically added to the item pool of each Universe.
///      - Users can request item issuance by selecting the desired universe,
///        and when requesting, they must burn NXPC according to the ratio.
contract ItemIssuance is ERC2771Context, NextOwnablePausable {
    /* solhint-disable var-name-mixedcase */

    enum Status {
        REQUESTED,
        CONFIRMED,
        REJECTED
    }

    struct Universe {
        string name;
        uint256 poolAmount;
    }

    struct Request {
        uint256 universe;
        uint256 id;
        address requester;
        uint256 itemAmount;
        uint256 basketAmount;
        uint256 nxpcAmount;
        Status status;
    }

    /// @notice NXPCAmountManager contract address
    INXPCAmountManager public immutable NXPCAmountManager;

    address public blackhole;
    /* solhint-enable var-name-mixedcase */

    /// @notice Information of universes
    Universe[] private universes;

    /// @notice Information of requests
    mapping(uint256 => Request) public requests;

    /// @notice A universe number of Item721 Contract
    mapping(address => uint256) public universeOfItem721;

    /// @notice Number of requests
    uint256 private requestLength;

    /// @notice Emitted when a new universe is created
    /// @param universe An id of universe
    /// @param name A name of universe
    event UniverseCreated(uint256 indexed universe, string indexed name);

    /// @notice Emitted when record results of adding ERC721 items to the item pool
    /// @param universe An id of universe
    /// @param amount Amount of item
    event ItemAdded(uint256 indexed universe, uint256 amount);

    /// @notice Emitted when ERC721 items requested from item pool
    /// @param universe An id of universe
    /// @param id An id of request
    /// @param requester Address of requester
    /// @param itemAmount Amount of item
    /// @param nxpcAmount Amount of NXPC
    event ItemRequested(
        uint256 indexed universe,
        uint256 indexed id,
        address requester,
        uint256 itemAmount,
        uint256 basketAmount,
        uint256 nxpcAmount
    );

    /// @notice Emitted when request confirmed
    /// @param universe An id of universe
    /// @param id An id of request
    event RequestConfirmed(uint256 indexed universe, uint256 indexed id);

    /// @notice Emitted when request rejected
    /// @param universe An id of universe
    /// @param id An id of request
    event RequestRejected(uint256 indexed universe, uint256 indexed id);

    /// @notice Emitted when request rejected
    /// @param previousBlackhole Address of previous blackhole
    /// @param newBlackhole Address of new blackhole
    event SetBlackhole(address previousBlackhole, address indexed newBlackhole);

    /// @notice Emitted when a item721 contract is registered
    /// @param universe A id of universe
    /// @param item721Contract A address of ERC721 contract
    event Item721ContractRegistered(uint256 indexed universe, address indexed item721Contract);

    /// @notice Emitted when a item721 contract is unregistered
    /// @param item721Contract A address of ERC721 contract
    event Item721ContractUnregistered(address indexed item721Contract);

    /// @notice Emitted when the base amount of 721 items is added
    /// @param universe A id of universe
    /// @param tokenAddress A address of ERC721 contract
    /// @param itemId A id of ERC721 items
    /// @param newLimitSupply A new base amount of ERC721 items in the item pool after adding
    event ItemBaseAmountAdded(
        uint256 indexed universe,
        address indexed tokenAddress,
        uint256 indexed itemId,
        uint256 newLimitSupply
    );

    /// @notice Check if the universe exists
    /// @param universe An id of universe
    modifier whenUniverseExists(uint256 universe) {
        require(1 <= universe && universe <= universes.length, "ItemIssuance/invalidUniverse: nonexistent universe");
        _;
    }

    modifier validAddress(address addr) {
        require(addr != address(0), "ItemIssuance/invalidAddress: couldn't be zero address");
        _;
    }

    /* solhint-disable var-name-mixedcase */

    constructor(
        address trustedForwarder,
        address _blackhole,
        address _NXPCAmountManager
    )
        ERC2771Context(trustedForwarder)
        validAddress(trustedForwarder)
        validAddress(_blackhole)
        validAddress(_NXPCAmountManager)
    {
        blackhole = _blackhole;
        NXPCAmountManager = INXPCAmountManager(_NXPCAmountManager);
    }
    /* solhint-enable var-name-mixedcase */
    /* trivial overrides */

    /// @notice Create a new universe
    /// @param name A name of universe
    function createUniverse(string calldata name) external onlyOwner {
        require(bytes(name).length > 0, "ItemIssuance/invalidRequest: length of name must be bigger than 0");
        universes.push(Universe({ name: name, poolAmount: 0 }));
        emit UniverseCreated(universes.length, name);
    }

    /// @notice Add item to pool
    /// @param universe An id of universe
    /// @param amount Amount of item
    function addItem(uint256 universe, uint256 amount) external whenUniverseExists(universe) whenExecutable {
        universes[universe - 1].poolAmount += amount;

        emit ItemAdded(universe, amount);
    }

    /// @notice Request an item by sending NXPC
    /// @param universe An id of universe
    /// @param itemAmount Amount of item
    /// @param basketAmount Amount of basket
    function requestItemIssuance(
        uint256 universe,
        uint256 itemAmount,
        uint256 basketAmount
    ) external payable whenUniverseExists(universe) {
        uint256 nxpcAmount = msg.value;
        address requester = _msgSender();

        require(universes[universe - 1].poolAmount >= itemAmount, "ItemIssuance/invalidAmount: too large amount");
        require(nxpcAmount > 0, "ItemIssuance/invalidAmount: zero value is not allowed");

        requestLength++;

        requests[requestLength] = Request({
            universe: universe,
            id: requestLength,
            requester: requester,
            itemAmount: itemAmount,
            basketAmount: basketAmount,
            nxpcAmount: nxpcAmount,
            status: Status.REQUESTED
        });

        emit ItemRequested(universe, requestLength, requester, itemAmount, basketAmount, nxpcAmount);
    }

    /// @notice After checking the request, approve or reject it
    /// @param universe An id of universe
    /// @param requestId An id of request
    /// @param isConfirmed Confirmed or rejected
    function confirmRequest(
        uint256 universe,
        uint256 requestId,
        bool isConfirmed
    ) external whenUniverseExists(universe) whenExecutable {
        Request storage request = requests[requestId];

        require(request.status == Status.REQUESTED, "ItemIssuance/invalidStatus: already confirmed");
        require(request.universe == universe, "ItemIssuance/invalidRequest: universe id doesn't match");

        address target;

        if (isConfirmed) {
            request.status = Status.CONFIRMED;
            target = blackhole;

            INXPCAmountManager(NXPCAmountManager).addBurnedAmount(request.nxpcAmount);
            universes[universe - 1].poolAmount -= request.itemAmount;

            emit RequestConfirmed(universe, requestId);
        } else {
            request.status = Status.REJECTED;
            target = request.requester;

            emit RequestRejected(universe, requestId);
        }

        Address.sendValue(payable(target), request.nxpcAmount);
    }

    /// @notice Sets a new blackhole address.
    /// @param newBlackhole The new blackhole address.
    function setBlackhole(address newBlackhole) external onlyOwner validAddress(newBlackhole) {
        emit SetBlackhole(blackhole, newBlackhole);
        blackhole = newBlackhole;
    }

    /// @notice Register a item721 contract
    /// @param universe A id of universe
    /// @param item721Contract A address of ERC721 contract
    function registerItem721Contract(
        uint256 universe,
        address item721Contract
    ) external whenUniverseExists(universe) validAddress(item721Contract) onlyOwner {
        _registerItem721Contract(universe, item721Contract);
    }

    /// @notice Unregister a item721 contract
    /// @param item721Contract A address of ERC721 contract
    function unregisterItem721Contract(address item721Contract) external onlyOwner {
        _unregisterItem721Contract(item721Contract);
    }

    /// @notice Increases the base amount of an item within the specified universe for ERC721 tokens
    /// @param itemId The ID of the item to increase the base amount for
    /// @param newLimitSupply The amount to add to the base amount of the item
    function addItem721BaseAmount(
        uint256 itemId,
        uint256 newLimitSupply
    ) external whenUniverseExists(universeOfItem721[_msgSender()]) {
        emit ItemBaseAmountAdded(universeOfItem721[_msgSender()], _msgSender(), itemId, newLimitSupply);
    }

    /// @notice Returns
    /// @param universe An id of universe
    /// @param amount Amount of item
    function expectAmount(uint256 universe, uint256 amount) public view whenUniverseExists(universe) returns (uint256) {
        uint256 itemAmount = universes[universe - 1].poolAmount;

        require(amount <= itemAmount, "ItemIssuance/invalidAmount: too large amount");

        return Math.ceilDiv(NXPCAmountManager.totalSupply() * amount, itemAmount);
    }

    /// @notice Returns the required NXPC amounts
    /// @param universe An id of universe
    function itemPoolAmount(uint256 universe) external view whenUniverseExists(universe) returns (uint256) {
        return universes[universe - 1].poolAmount;
    }

    /// @notice Retrieve the name of a specific universe
    /// @param universe The identifier of the universe to retrieve the name for
    /// @return string The name of the specified universe
    function universeName(uint256 universe) external view whenUniverseExists(universe) returns (string memory) {
        return universes[universe - 1].name;
    }

    /// @notice Register a item721 contract
    /// @param universe A id of universe
    /// @param item721Contract A address of ERC721 contract
    function _registerItem721Contract(uint256 universe, address item721Contract) internal {
        require(universeOfItem721[item721Contract] == 0, "ItemIssuance/invalidAddress: already registered");
        universeOfItem721[item721Contract] = universe;

        emit Item721ContractRegistered(universe, item721Contract);
    }

    /// @notice Unregister a item721 contract
    /// @param item721Contract A address of ERC721 contract
    function _unregisterItem721Contract(address item721Contract) internal {
        require(universeOfItem721[item721Contract] != 0, "ItemIssuance/invalidAddress: not registered");
        delete universeOfItem721[item721Contract];

        emit Item721ContractUnregistered(item721Contract);
    }

    /* trivial overrides */

    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}


// File contracts/Creator/interfaces/ICreatorFactory.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;


/// @title ICreatorFactory - Interface of CreatorFactory
interface ICreatorFactory {
    struct Creator {
        string name;
        address account;
    }
    struct DApp {
        uint32 creatorId;
        bool isActive;
        address account;
        string name;
    }
    struct Reward {
        address payable creatorAddress;
        uint256 nxpcAmount;
        IERC20[] tokens;
        uint256[] amounts;
    }

    event CreatorAdded(uint32 id, string name, address account);
    event CreatorNameChanged(uint32 id, string previousName, string newName);
    event CreatorOfDAppChanged(uint32 dAppId_, uint32 creatorId_);
    event DAppAdded(uint32 id, string name, address account);
    event DAppNameChanged(uint32 id, string previousName, string newName);
    event DAppOwnerChanged(address previousDAppOwner, address newDAppOwner);
    event DAppActivationChanged(uint32 id, bool newIsActive);
    event NXPCRewardAllocated(address indexed account, uint256 amount);
    event ERC20RewardAllocated(address indexed account, IERC20 indexed token, uint256 amount);

    function addCreator(string calldata name, address[] memory owners, uint256 threshold) external;

    function addDApp(uint32 creatorId_, string calldata name, address executor) external;

    function setCreatorName(uint32 id, string calldata newName) external;

    function setDAppName(uint32 id, string calldata newName) external;

    function setDAppOwner(address newDAppOwner) external;

    function setDAppActivation(uint32 id, bool isActive) external;

    function setCreatorOfDApp(uint32 dAppId_, uint32 creatorId_) external;

    function isActiveDApp(uint32 dAppId_) external view returns (bool);

    function dAppOwner() external view returns (address);

    function creatorAddress(uint32 creatorId_) external view returns (address);

    function creatorAddressOfDApp(address dAppAddress_) external view returns (address);

    function creatorAddressOfDApp(uint32 dAppId_) external view returns (address);

    function creatorId(address creatorAddress_) external view returns (uint32);

    function creatorIdOfDApp(address dAppAddress_) external view returns (uint32);

    function creatorIdOfDApp(uint32 dAppId_) external view returns (uint32);

    function creatorName(address creatorAddress_) external view returns (string memory);

    function creatorName(uint32 creatorId_) external view returns (string memory);

    function dAppAddress(uint32 dAppId_) external view returns (address);

    function dAppId(address dAppAddress_) external view returns (uint32);

    function dAppName(address dAppAddress_) external view returns (string memory);

    function dAppName(uint32 dAppId_) external view returns (string memory);

    function creatorBeacon() external view returns (address);

    function itemIssuance() external view returns (ItemIssuance);

    function isConnected(uint32 creatorId_, uint32 dAppId_) external view returns (bool);

    function isConnected(uint32 creatorId_, address dAppAddress_) external view returns (bool);

    function isConnected(address crestorAddress_, uint32 dAppId_) external view returns (bool);

    function isConnected(address crestorAddress_, address dAppAddress_) external view returns (bool);
}


// File contracts/Creator/DAppRewardAllocationWallet/DAppRewardAllocationWallet.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;









/// @title DAppRewardAllocationWallet - A Contract for activities in a DAPP
/// @dev Main feature
///      - Mainly distributing assets to users
///      - Exec contracts are used to perform actions.
contract DAppRewardAllocationWallet is ERC2771Context, Exec, NextOwnablePausable, ERC721Holder, ERC1155Holder {
    using SafeERC20 for IERC20;

    ICreatorFactory public immutable creatorFactory;

    constructor(address trustedForwarder) ERC2771Context(trustedForwarder) {
        creatorFactory = ICreatorFactory(_msgSender());
    }

    /// @notice Send ERC20 tokens back to the creator
    /// @dev It is implemented separately because processing related to NonWithdrawableERC20 needs to happen alongside token transfer.
    /// @param token ERC20 token address
    /// @param amount Amount of ERC20 token
    function deallocateERC20(IERC20 token, uint256 amount) external whenExecutable {
        address creatorWallet = creatorFactory.creatorAddressOfDApp(address(this));
        token.safeTransfer(creatorWallet, amount);
    }

    /// @notice Get the dApp Id
    /// @return uint32 dApp Id
    function dAppId() external view returns (uint32) {
        return creatorFactory.dAppId(address(this));
    }

    function _beforeExec() internal override whenExecutable {}

    /* trivial overrides */
    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}
