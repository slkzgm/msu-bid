// SPDX-License-Identifier: MIT
pragma solidity 0.8.19;


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)
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


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)
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


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)
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


// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)
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

interface IERC721 is IERC165 {
    /**
     * @dev Emitted when `tokenId` token is transferred from `from` to `to`.
     */
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables `approved` to manage the `tokenId` token.
     */
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables or disables (`approved`) `operator` to manage all of its assets.
     */
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /**
     * @dev Returns the number of tokens in ``owner``'s account.
     */
    function balanceOf(address owner) external view returns (uint256 balance);

    /**
     * @dev Returns the owner of the `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function ownerOf(uint256 tokenId) external view returns (address owner);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes calldata data
    ) external;

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must have been allowed to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Transfers `tokenId` token from `from` to `to`.
     *
     * WARNING: Note that the caller is responsible to confirm that the recipient is capable of receiving ERC721
     * or else they may be permanently lost. Usage of {safeTransferFrom} prevents loss, though the caller must
     * understand this adds an external call which potentially creates a reentrancy vulnerability.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Gives permission to `to` to transfer `tokenId` token to another account.
     * The approval is cleared when the token is transferred.
     *
     * Only a single account can be approved at a time, so approving the zero address clears previous approvals.
     *
     * Requirements:
     *
     * - The caller must own the token or be an approved operator.
     * - `tokenId` must exist.
     *
     * Emits an {Approval} event.
     */
    function approve(address to, uint256 tokenId) external;

    /**
     * @dev Approve or remove `operator` as an operator for the caller.
     * Operators can call {transferFrom} or {safeTransferFrom} for any token owned by the caller.
     *
     * Requirements:
     *
     * - The `operator` cannot be the caller.
     *
     * Emits an {ApprovalForAll} event.
     */
    function setApprovalForAll(address operator, bool _approved) external;

    /**
     * @dev Returns the account approved for `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function getApproved(uint256 tokenId) external view returns (address operator);

    /**
     * @dev Returns if the `operator` is allowed to manage all of the assets of `owner`.
     *
     * See {setApprovalForAll}
     */
    function isApprovedForAll(address owner, address operator) external view returns (bool);
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)
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


// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/Math.sol)
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

library Strings {
    bytes16 private constant _SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = Math.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            /// @solidity memory-safe-assembly
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                /// @solidity memory-safe-assembly
                assembly {
                    mstore8(ptr, byte(mod(value, 10), _SYMBOLS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, Math.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), _ADDRESS_LENGTH);
    }
}


// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC721/IERC721.sol)
/**
 * @dev Required interface of an ERC721 compliant contract.
 */


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC721/IERC721Receiver.sol)
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


// OpenZeppelin Contracts v4.4.1 (token/ERC721/extensions/IERC721Metadata.sol)
/**
 * @title ERC-721 Non-Fungible Token Standard, optional metadata extension
 * @dev See https://eips.ethereum.org/EIPS/eip-721
 */
interface IERC721Metadata is IERC721 {
    /**
     * @dev Returns the token collection name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the token collection symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the Uniform Resource Identifier (URI) for `tokenId` token.
     */
    function tokenURI(uint256 tokenId) external view returns (string memory);
}


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Strings.sol)
/**
 * @dev String operations.
 */


// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)
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

contract ERC721 is Context, ERC165, IERC721, IERC721Metadata {
    using Address for address;
    using Strings for uint256;

    // Token name
    string private _name;

    // Token symbol
    string private _symbol;

    // Mapping from token ID to owner address
    mapping(uint256 => address) private _owners;

    // Mapping owner address to token count
    mapping(address => uint256) private _balances;

    // Mapping from token ID to approved address
    mapping(uint256 => address) private _tokenApprovals;

    // Mapping from owner to operator approvals
    mapping(address => mapping(address => bool)) private _operatorApprovals;

    /**
     * @dev Initializes the contract by setting a `name` and a `symbol` to the token collection.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override(ERC165, IERC165) returns (bool) {
        return
            interfaceId == type(IERC721).interfaceId ||
            interfaceId == type(IERC721Metadata).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    /**
     * @dev See {IERC721-balanceOf}.
     */
    function balanceOf(address owner) public view virtual override returns (uint256) {
        require(owner != address(0), "ERC721: address zero is not a valid owner");
        return _balances[owner];
    }

    /**
     * @dev See {IERC721-ownerOf}.
     */
    function ownerOf(uint256 tokenId) public view virtual override returns (address) {
        address owner = _ownerOf(tokenId);
        require(owner != address(0), "ERC721: invalid token ID");
        return owner;
    }

    /**
     * @dev See {IERC721Metadata-name}.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev See {IERC721Metadata-symbol}.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev See {IERC721Metadata-tokenURI}.
     */
    function tokenURI(uint256 tokenId) public view virtual override returns (string memory) {
        _requireMinted(tokenId);

        string memory baseURI = _baseURI();
        return bytes(baseURI).length > 0 ? string(abi.encodePacked(baseURI, tokenId.toString())) : "";
    }

    /**
     * @dev Base URI for computing {tokenURI}. If set, the resulting URI for each
     * token will be the concatenation of the `baseURI` and the `tokenId`. Empty
     * by default, can be overridden in child contracts.
     */
    function _baseURI() internal view virtual returns (string memory) {
        return "";
    }

    /**
     * @dev See {IERC721-approve}.
     */
    function approve(address to, uint256 tokenId) public virtual override {
        address owner = ERC721.ownerOf(tokenId);
        require(to != owner, "ERC721: approval to current owner");

        require(
            _msgSender() == owner || isApprovedForAll(owner, _msgSender()),
            "ERC721: approve caller is not token owner or approved for all"
        );

        _approve(to, tokenId);
    }

    /**
     * @dev See {IERC721-getApproved}.
     */
    function getApproved(uint256 tokenId) public view virtual override returns (address) {
        _requireMinted(tokenId);

        return _tokenApprovals[tokenId];
    }

    /**
     * @dev See {IERC721-setApprovalForAll}.
     */
    function setApprovalForAll(address operator, bool approved) public virtual override {
        _setApprovalForAll(_msgSender(), operator, approved);
    }

    /**
     * @dev See {IERC721-isApprovedForAll}.
     */
    function isApprovedForAll(address owner, address operator) public view virtual override returns (bool) {
        return _operatorApprovals[owner][operator];
    }

    /**
     * @dev See {IERC721-transferFrom}.
     */
    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) public virtual override {
        //solhint-disable-next-line max-line-length
        require(_isApprovedOrOwner(_msgSender(), tokenId), "ERC721: caller is not token owner or approved");

        _transfer(from, to, tokenId);
    }

    /**
     * @dev See {IERC721-safeTransferFrom}.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) public virtual override {
        safeTransferFrom(from, to, tokenId, "");
    }

    /**
     * @dev See {IERC721-safeTransferFrom}.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes memory data
    ) public virtual override {
        require(_isApprovedOrOwner(_msgSender(), tokenId), "ERC721: caller is not token owner or approved");
        _safeTransfer(from, to, tokenId, data);
    }

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * `data` is additional data, it has no specified format and it is sent in call to `to`.
     *
     * This internal function is equivalent to {safeTransferFrom}, and can be used to e.g.
     * implement alternative mechanisms to perform token transfer, such as signature-based.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function _safeTransfer(
        address from,
        address to,
        uint256 tokenId,
        bytes memory data
    ) internal virtual {
        _transfer(from, to, tokenId);
        require(_checkOnERC721Received(from, to, tokenId, data), "ERC721: transfer to non ERC721Receiver implementer");
    }

    /**
     * @dev Returns the owner of the `tokenId`. Does NOT revert if token doesn't exist
     */
    function _ownerOf(uint256 tokenId) internal view virtual returns (address) {
        return _owners[tokenId];
    }

    /**
     * @dev Returns whether `tokenId` exists.
     *
     * Tokens can be managed by their owner or approved accounts via {approve} or {setApprovalForAll}.
     *
     * Tokens start existing when they are minted (`_mint`),
     * and stop existing when they are burned (`_burn`).
     */
    function _exists(uint256 tokenId) internal view virtual returns (bool) {
        return _ownerOf(tokenId) != address(0);
    }

    /**
     * @dev Returns whether `spender` is allowed to manage `tokenId`.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function _isApprovedOrOwner(address spender, uint256 tokenId) internal view virtual returns (bool) {
        address owner = ERC721.ownerOf(tokenId);
        return (spender == owner || isApprovedForAll(owner, spender) || getApproved(tokenId) == spender);
    }

    /**
     * @dev Safely mints `tokenId` and transfers it to `to`.
     *
     * Requirements:
     *
     * - `tokenId` must not exist.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function _safeMint(address to, uint256 tokenId) internal virtual {
        _safeMint(to, tokenId, "");
    }

    /**
     * @dev Same as {xref-ERC721-_safeMint-address-uint256-}[`_safeMint`], with an additional `data` parameter which is
     * forwarded in {IERC721Receiver-onERC721Received} to contract recipients.
     */
    function _safeMint(
        address to,
        uint256 tokenId,
        bytes memory data
    ) internal virtual {
        _mint(to, tokenId);
        require(
            _checkOnERC721Received(address(0), to, tokenId, data),
            "ERC721: transfer to non ERC721Receiver implementer"
        );
    }

    /**
     * @dev Mints `tokenId` and transfers it to `to`.
     *
     * WARNING: Usage of this method is discouraged, use {_safeMint} whenever possible
     *
     * Requirements:
     *
     * - `tokenId` must not exist.
     * - `to` cannot be the zero address.
     *
     * Emits a {Transfer} event.
     */
    function _mint(address to, uint256 tokenId) internal virtual {
        require(to != address(0), "ERC721: mint to the zero address");
        require(!_exists(tokenId), "ERC721: token already minted");

        _beforeTokenTransfer(address(0), to, tokenId, 1);

        // Check that tokenId was not minted by `_beforeTokenTransfer` hook
        require(!_exists(tokenId), "ERC721: token already minted");

        unchecked {
            // Will not overflow unless all 2**256 token ids are minted to the same owner.
            // Given that tokens are minted one by one, it is impossible in practice that
            // this ever happens. Might change if we allow batch minting.
            // The ERC fails to describe this case.
            _balances[to] += 1;
        }

        _owners[tokenId] = to;

        emit Transfer(address(0), to, tokenId);

        _afterTokenTransfer(address(0), to, tokenId, 1);
    }

    /**
     * @dev Destroys `tokenId`.
     * The approval is cleared when the token is burned.
     * This is an internal function that does not check if the sender is authorized to operate on the token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     *
     * Emits a {Transfer} event.
     */
    function _burn(uint256 tokenId) internal virtual {
        address owner = ERC721.ownerOf(tokenId);

        _beforeTokenTransfer(owner, address(0), tokenId, 1);

        // Update ownership in case tokenId was transferred by `_beforeTokenTransfer` hook
        owner = ERC721.ownerOf(tokenId);

        // Clear approvals
        delete _tokenApprovals[tokenId];

        unchecked {
            // Cannot overflow, as that would require more tokens to be burned/transferred
            // out than the owner initially received through minting and transferring in.
            _balances[owner] -= 1;
        }
        delete _owners[tokenId];

        emit Transfer(owner, address(0), tokenId);

        _afterTokenTransfer(owner, address(0), tokenId, 1);
    }

    /**
     * @dev Transfers `tokenId` from `from` to `to`.
     *  As opposed to {transferFrom}, this imposes no restrictions on msg.sender.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     *
     * Emits a {Transfer} event.
     */
    function _transfer(
        address from,
        address to,
        uint256 tokenId
    ) internal virtual {
        require(ERC721.ownerOf(tokenId) == from, "ERC721: transfer from incorrect owner");
        require(to != address(0), "ERC721: transfer to the zero address");

        _beforeTokenTransfer(from, to, tokenId, 1);

        // Check that tokenId was not transferred by `_beforeTokenTransfer` hook
        require(ERC721.ownerOf(tokenId) == from, "ERC721: transfer from incorrect owner");

        // Clear approvals from the previous owner
        delete _tokenApprovals[tokenId];

        unchecked {
            // `_balances[from]` cannot overflow for the same reason as described in `_burn`:
            // `from`'s balance is the number of token held, which is at least one before the current
            // transfer.
            // `_balances[to]` could overflow in the conditions described in `_mint`. That would require
            // all 2**256 token ids to be minted, which in practice is impossible.
            _balances[from] -= 1;
            _balances[to] += 1;
        }
        _owners[tokenId] = to;

        emit Transfer(from, to, tokenId);

        _afterTokenTransfer(from, to, tokenId, 1);
    }

    /**
     * @dev Approve `to` to operate on `tokenId`
     *
     * Emits an {Approval} event.
     */
    function _approve(address to, uint256 tokenId) internal virtual {
        _tokenApprovals[tokenId] = to;
        emit Approval(ERC721.ownerOf(tokenId), to, tokenId);
    }

    /**
     * @dev Approve `operator` to operate on all of `owner` tokens
     *
     * Emits an {ApprovalForAll} event.
     */
    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual {
        require(owner != operator, "ERC721: approve to caller");
        _operatorApprovals[owner][operator] = approved;
        emit ApprovalForAll(owner, operator, approved);
    }

    /**
     * @dev Reverts if the `tokenId` has not been minted yet.
     */
    function _requireMinted(uint256 tokenId) internal view virtual {
        require(_exists(tokenId), "ERC721: invalid token ID");
    }

    /**
     * @dev Internal function to invoke {IERC721Receiver-onERC721Received} on a target address.
     * The call is not executed if the target address is not a contract.
     *
     * @param from address representing the previous owner of the given token ID
     * @param to target address that will receive the tokens
     * @param tokenId uint256 ID of the token to be transferred
     * @param data bytes optional data to send along with the call
     * @return bool whether the call correctly returned the expected magic value
     */
    function _checkOnERC721Received(
        address from,
        address to,
        uint256 tokenId,
        bytes memory data
    ) private returns (bool) {
        if (to.isContract()) {
            try IERC721Receiver(to).onERC721Received(_msgSender(), from, tokenId, data) returns (bytes4 retval) {
                return retval == IERC721Receiver.onERC721Received.selector;
            } catch (bytes memory reason) {
                if (reason.length == 0) {
                    revert("ERC721: transfer to non ERC721Receiver implementer");
                } else {
                    /// @solidity memory-safe-assembly
                    assembly {
                        revert(add(32, reason), mload(reason))
                    }
                }
            }
        } else {
            return true;
        }
    }

    /**
     * @dev Hook that is called before any token transfer. This includes minting and burning. If {ERC721Consecutive} is
     * used, the hook may be called as part of a consecutive (batch) mint, as indicated by `batchSize` greater than 1.
     *
     * Calling conditions:
     *
     * - When `from` and `to` are both non-zero, ``from``'s tokens will be transferred to `to`.
     * - When `from` is zero, the tokens will be minted for `to`.
     * - When `to` is zero, ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     * - `batchSize` is non-zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256, /* firstTokenId */
        uint256 batchSize
    ) internal virtual {
        if (batchSize > 1) {
            if (from != address(0)) {
                _balances[from] -= batchSize;
            }
            if (to != address(0)) {
                _balances[to] += batchSize;
            }
        }
    }

    /**
     * @dev Hook that is called after any token transfer. This includes minting and burning. If {ERC721Consecutive} is
     * used, the hook may be called as part of a consecutive (batch) mint, as indicated by `batchSize` greater than 1.
     *
     * Calling conditions:
     *
     * - When `from` and `to` are both non-zero, ``from``'s tokens were transferred to `to`.
     * - When `from` is zero, the tokens were minted for `to`.
     * - When `to` is zero, ``from``'s tokens were burned.
     * - `from` and `to` are never both zero.
     * - `batchSize` is non-zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 firstTokenId,
        uint256 batchSize
    ) internal virtual {}
}


// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC721/ERC721.sol)
/**
 * @dev Implementation of https://eips.ethereum.org/EIPS/eip-721[ERC721] Non-Fungible Token Standard, including
 * the Metadata extension, but not including the Enumerable extension, which is available separately as
 * {ERC721Enumerable}.
 */


// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)
/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */

abstract contract ERC721Pausable is ERC721, Pausable {
    /**
     * @dev See {ERC721-_beforeTokenTransfer}.
     *
     * Requirements:
     *
     * - the contract must not be paused.
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 firstTokenId,
        uint256 batchSize
    ) internal virtual override {
        super._beforeTokenTransfer(from, to, firstTokenId, batchSize);

        require(!paused(), "ERC721Pausable: token transfer while paused");
    }
}

contract ApproveController is ERC2771Context, NextOwnablePausable {
    struct Approval {
        bool approved;
        uint256 approveDate;
    }

    mapping(address => Approval) private _approvals;

    mapping(address => bool) private _allowlisted;

    event SetApprove(address indexed account, bool newApproved);
    event SetAllowlisted(address indexed account, bool newAllowed);

    constructor(address trustedForwarder) ERC2771Context(trustedForwarder) {}

    /// @notice Sets the approval of the caller. Users will call this function to approve all their assets.
    function setApprove(bool newApproved) public whenNotPaused {
        _approvals[_msgSender()] = Approval(newApproved, block.timestamp);

        emit SetApprove(_msgSender(), newApproved);
    }

    /// @notice Sets whether the given contract is allowlisted.
    /// Users can directly approve their assets to only the allowlisted contracts. Only owner can call.
    /// Allowlist has nothing to do with setApprove.
    function setAllowlist(address account, bool newAllowed) public onlyOwner {
        _allowlisted[account] = newAllowed;

        emit SetAllowlisted(account, newAllowed);
    }

    /// @notice Returns whether the given address has approved.
    function isApproved(address account) public view returns (bool) {
        return _approvals[account].approved;
    }

    /// @notice Returns the timestamp when the given address approved.
    function getApproveDate(address account) public view returns (uint256) {
        return _approvals[account].approveDate;
    }

    /// @notice Returns whether the given contract address is allowlisted.
    function isAllowlisted(address account) public view returns (bool) {
        return _allowlisted[account];
    }

    /* trivial overrides */

    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}

contract ApproveControlled is Ownable {
    ApproveController public immutable controller;

    mapping(address => bool) private _isApprovedOperator;

    event OperatorApproved(address indexed operator);
    event OperatorDisapproved(address indexed operator);

    constructor(ApproveController controller_) {
        controller = controller_;
    }

    /// @notice Reverts when the given contract address is not allowlisted.
    modifier onlyAllowlisted(address account) {
        require(controller.isAllowlisted(account), "ApproveControlled/notAllowlisted: account is not allowlisted");
        _;
    }

    /// @notice Sets the given address as approved operator(spender) of tokens owned by users who approved their assets to
    /// ApproveController. Only owner can call.
    function approveOperator(address operator) external onlyOwner {
        if (isApprovedOperator(operator)) return;
        _isApprovedOperator[operator] = true;
        emit OperatorApproved(operator);
    }

    /// @notice Unsets the given address from approved operator.
    function disapproveOperator(address operator) external onlyOwner {
        if (!isApprovedOperator(operator)) return;
        _isApprovedOperator[operator] = false;
        emit OperatorDisapproved(operator);
    }

    /// @notice Returns whether the given address is approved operator.
    function isApprovedOperator(address account) public view returns (bool) {
        return _isApprovedOperator[account];
    }

    /// @notice Returns whether the given address has approved ther assets to ApproveController.
    function _isApprover(address account) internal view returns (bool) {
        return controller.isApproved(account);
    }
}

abstract contract ERC721ApproveControlled is ERC721, ApproveControlled {
    /// @notice Overrides isApprovedForAll function to return true when the transfer is approved by ApproveController.
    function isApprovedForAll(address owner, address operator) public view virtual override returns (bool) {
        if (isApprovedOperator(operator) && _isApprover(owner)) return true;
        return ERC721.isApprovedForAll(owner, operator);
    }

    /// @notice Restricts the spender to be allowlisted. Users cannot modify approval to non-allowlisted spender.
    function _approve(address to, uint256 tokenId) internal virtual override onlyAllowlisted(to) {
        ERC721._approve(to, tokenId);
    }

    /// @notice Restricts the spender to be allowlisted. Users cannot modify approval to non-allowlisted spender.
    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual override onlyAllowlisted(operator) {
        ERC721._setApprovalForAll(owner, operator, approved);
    }
}

interface INXPCAmountManager {
    function totalSupply() external view returns (uint256);

    function addBurnedAmount(uint256 amount) external;

    function addMintedAmount(uint256 amount) external;
}

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

contract MaplestoryEquip is
    ERC2771Context,
    ERC721("MaplestoryEquip", "MSE"),
    NextOwnablePausable,
    ERC721Pausable,
    ERC721ApproveControlled {
    using Strings for uint256;

    struct Token {
        uint64 itemId;
        uint64 number;
    }

    // limitSupply >= totalSupply + burnedAmount
    struct Item {
        uint64 totalSupply;
        uint64 limitSupply;
        uint64 burnedAmount;
    }

    struct Mint {
        uint64 itemId;
        uint256 tokenId;
    }

    modifier onlyExistToken(uint256 tokenId) {
        require(_exists(tokenId), "MaplestoryEquip/tokenNotExists: token is not exist");
        _;
    }

    modifier onlyExistItem(uint64 itemId) {
        require(_items[itemId].limitSupply != 0, "MaplestoryEquip/itemNotExists: item is not exist");
        _;
    }

    ItemIssuance private immutable _itemIssuance;
    string private _defaultBaseURI;
    uint256 private _totalSupply;
    uint256 private _burnedAmount;

    // solhint-disable-next-line var-name-mixedcase
    mapping(uint256 => Token) private _tokens;
    mapping(uint64 => Item) private _items;
    mapping(uint64 => string) private _itemBaseURIs;

    event ItemLimitSupply(uint64 indexed itemId, uint64 previousLimitSupply, uint64 newLimitSupply);
    event ItemCreated(uint256 indexed tokenId, uint64 indexed itemId, uint64 number);
    event DefaultBaseURIChanged(string previousURI, string newURI);
    event ItemBaseURIChanged(uint64 indexed itemId, string previousURI, string newURI);
    event RetrievedERC721(address from, address to, uint256 tokenId, string reason);

    constructor(
        address trustedForwarder,
        ApproveController controller_,
        ItemIssuance itemIssuance_,
        string memory defaultBaseURI
    ) ERC2771Context(trustedForwarder) ApproveControlled(controller_) {
        _itemIssuance = itemIssuance_;
        _defaultBaseURI = defaultBaseURI;
    }

    /// @notice Mints new MaplestoryEquip token.
    /// @param to Address to receive token.
    /// @param itemId Token's item id.
    /// @param tokenId Token's id.
    function mint(address to, uint64 itemId, uint256 tokenId) external whenExecutable {
        _mint(to, itemId, tokenId);
    }

    /// @notice Batch function of {Mint}.
    /// @dev Instead of checking length of the `itemId` and `tokenId`, uses `Mint` struct.
    function mintBatch(address to, Mint[] memory mints) external whenExecutable {
        uint256 mintsLength = mints.length;
        for (uint256 i; i < mintsLength; ) {
            _mint(to, mints[i].itemId, mints[i].tokenId);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Batch function of {Burn}.
    function burnBatch(uint256[] memory tokenIds) external {
        uint256 tokenIdsLength = tokenIds.length;
        for (uint256 i; i < tokenIdsLength; ) {
            burn(tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Batch function of {ERC721-safeTransferFrom}.
    function safeBatchTransferFrom(address from, address to, uint256[] memory tokenIds) external {
        uint256 tokenIdsLength = tokenIds.length;
        for (uint256 i; i < tokenIdsLength; ) {
            safeTransferFrom(from, to, tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Set `_defaultBaseURI`.
    /// @param newURI String of the new `_defaultBaseURI`.
    function setDefaultURI(string memory newURI) external whenExecutable {
        string memory previousURI = _defaultBaseURI;
        _defaultBaseURI = newURI;
        emit DefaultBaseURIChanged(previousURI, _defaultBaseURI);
    }

    /// @notice Set `_itemBaseURIs`.
    /// @param itemId token's item id.
    /// @param newURI String of the new item's base uri.
    function setItemURI(uint64 itemId, string memory newURI) external whenExecutable {
        string memory previousURI = _itemBaseURIs[itemId];
        _itemBaseURIs[itemId] = newURI;
        emit ItemBaseURIChanged(itemId, previousURI, _itemBaseURIs[itemId]);
    }

    /// @notice Set `item.limitSupply`.
    /// @dev Can set only once for each item.
    /// @param itemId Token's item id.
    /// @param newLimitSupply New limitSupply of the item.
    /// @param isItemBase Items included in itemBase
    function setLimitSupply(uint64 itemId, uint64 newLimitSupply, bool isItemBase) external whenExecutable {
        Item storage item = _items[itemId];
        require(item.limitSupply == 0, "MaplestoryEquip/setLimitSupply: limit supply is already set");

        emit ItemLimitSupply(itemId, item.limitSupply, newLimitSupply);

        item.limitSupply = newLimitSupply;

        if (isItemBase) {
            _itemIssuance.addItem721BaseAmount(itemId, newLimitSupply);
        }
    }

    /// @notice Retrieve equip item by owner.
    /// @param from Address of the item owner.
    /// @param to Address of the item receiver.
    /// @param tokenId Token's id.
    /// @param reason Reason of the retrieval.
    function retrieveERC721(address from, address to, uint256 tokenId, string memory reason) external onlyOwner {
        safeTransferFrom(from, to, tokenId, "");
        emit RetrievedERC721(from, to, tokenId, reason);
    }

    /// @notice Returns `_itemIssuance`.
    /// @return ItemIssuance Address of the `_itemIssuance`.
    function itemIssuance() external view returns (ItemIssuance) {
        return _itemIssuance;
    }

    /// @notice Returns `_totalSupply`.
    /// @return uint256 Number of `_totalSupply`.
    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    /// @notice Returns `_burnedAmount`.
    /// @return uint256 Sum of the `burnedAmount` of all items.
    function burnedAmount() external view returns (uint256) {
        return _burnedAmount;
    }

    /// @notice Returns `itemId` of token.
    /// @param tokenId Token's id.
    /// @return uint64 Number of the token's `itemId`.
    function tokenItemId(uint256 tokenId) external view onlyExistToken(tokenId) returns (uint64) {
        return _tokens[tokenId].itemId;
    }

    /// @notice Returns the number of token.
    /// @dev `TokenNumber` indicates the minting order of the token within the item which it belongs to.
    /// @param tokenId Token's id.
    /// @return uint64 Number of the token's `number`.
    function tokenNumber(uint256 tokenId) external view onlyExistToken(tokenId) returns (uint64) {
        return _tokens[tokenId].number;
    }

    /// @notice Returns `totalSupply` of item.
    /// @param itemId Token's item id.
    /// @return uint64 Number of item's `totalSupply`.
    function itemTotalSupply(uint64 itemId) external view onlyExistItem(itemId) returns (uint64) {
        return _items[itemId].totalSupply;
    }

    /// @notice Returns `limitSupply` of item.
    /// @param itemId Token's item id.
    /// @return uint64 Number of item's `limitSupply`.
    function itemLimitSupply(uint64 itemId) external view onlyExistItem(itemId) returns (uint64) {
        return _items[itemId].limitSupply;
    }

    /// @notice Returns `burnedAmount` of item.
    /// @param itemId Token's item id.
    /// @return uint64 Number of item's `burnedAmount`.
    function itemBurnedAmount(uint64 itemId) external view onlyExistItem(itemId) returns (uint64) {
        return _items[itemId].burnedAmount;
    }

    /// @notice Returns list of the tokens owner.
    /// @param tokenIds List of the token ids.
    /// @return address Address list of the tokens owner.
    function ownerOfBatch(uint256[] memory tokenIds) external view returns (address[] memory) {
        uint256 tokenIdsLength = tokenIds.length;
        address[] memory batchOwners = new address[](tokenIdsLength);

        for (uint256 i; i < tokenIdsLength; ++i) {
            batchOwners[i] = ownerOf(tokenIds[i]);
        }

        return batchOwners;
    }

    /// @notice Burns MaplestoryEquip token.
    /// @param tokenId Token's id that to be burned.
    function burn(uint256 tokenId) public {
        // solhint-disable-next-line reason-string
        require(
            _isApprovedOrOwner(_msgSender(), tokenId),
            "MaplestoryEquip/burnForbidden: caller is neither the token owner, approved"
        );

        uint64 itemId = _tokens[tokenId].itemId;
        delete _tokens[tokenId];
        unchecked {
            _items[itemId].totalSupply--;
            _items[itemId].burnedAmount++;
        }
        unchecked {
            _totalSupply--;
            _burnedAmount++;
        }

        _burn(tokenId);
    }

    /// @notice Returns token's uri.
    /// @dev Returns `_itemBaseURIs` if the base uri of item is set. Otherwise returns `_defaultBaseURI`.
    /// @param tokenId Token's id.
    /// @return string String of the token uri.
    function tokenURI(uint256 tokenId) public view override returns (string memory) {
        require(_exists(tokenId), "MaplestoryEquip/uriInvalidID: URI query for nonexistent token");

        uint64 itemId = _tokens[tokenId].itemId;
        string memory uri = bytes(_itemBaseURIs[itemId]).length > 0 ? _itemBaseURIs[itemId] : _defaultBaseURI;

        return string(abi.encodePacked(uri, tokenId.toString(), ".json"));
    }

    /// @notice Returns token owner.
    /// @param tokenId Token's id.
    /// @return address Address of the token's current owner.
    function ownerOf(uint256 tokenId) public view virtual override returns (address) {
        address owner = _ownerOf(tokenId);
        if (owner == address(0)) {
            // nx-errors-ignore
            revert(
                string(abi.encodePacked("MaplestoryEquip/ownerOfInvalidID: invalid token ID(", tokenId.toString(), ")"))
            );
        }
        return owner;
    }

    /// @notice Mints new MaplestoryEquip token.
    /// @param to Address to receive minted token.
    /// @param itemId Item id of the new token.
    /// @param tokenId Token id of the new token.
    function _mint(address to, uint64 itemId, uint256 tokenId) internal {
        Item storage item = _items[itemId];
        // solhint-disable-next-line reason-string
        require(
            item.totalSupply + item.burnedAmount < item.limitSupply,
            "MaplestoryEquip/mintInvalidItem: supply limit exceeded or minting for invalid item ID"
        );

        uint64 itemNumber;
        unchecked {
            item.totalSupply++;
            itemNumber = item.totalSupply + item.burnedAmount;
            _tokens[tokenId] = Token(itemId, itemNumber);
            _totalSupply++;
        }
        ERC721._safeMint(to, tokenId);

        emit ItemCreated(tokenId, itemId, itemNumber);
    }

    /// @notice See {ERC721Pausable-_beforeTokenTransfer}.
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 tokenId,
        uint256 batchSize
    ) internal override(ERC721, ERC721Pausable) {
        ERC721Pausable._beforeTokenTransfer(from, to, tokenId, batchSize);
    }

    /* trivial overrides */

    /// @notice See {ERC721ApproveControlled-isApprovedForAll}.
    function isApprovedForAll(
        address owner_,
        address operator
    ) public view override(ERC721, ERC721ApproveControlled) returns (bool) {
        if (owner() == _msgSender()) {
            return true;
        }
        return ERC721ApproveControlled.isApprovedForAll(owner_, operator);
    }

    /// @notice See {ERC721ApproveControlled-_approve}
    function _approve(address to, uint256 tokenId) internal virtual override(ERC721, ERC721ApproveControlled) {
        ERC721ApproveControlled._approve(to, tokenId);
    }

    /// @notice See {ERC721ApproveControlled-_setApprovalForAll}.
    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual override(ERC721, ERC721ApproveControlled) {
        ERC721ApproveControlled._setApprovalForAll(owner, operator, approved);
    }

    /// @notice See {ERC2771Context-_msgSender}.
    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    /// @notice See {ERC2771Context-_msgData}.
    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}

library MinProxyGetCode {
    function getCode(address impl) internal pure returns (bytes memory) {
        return abi.encodePacked("`-\x80`\t=9=\xf36==7===6=s", impl, "Z\xf4=\x82\x80>\x90=\x91`+W\xfd[\xf3");
    }
}

library MinBeaconProxyGetCode {
    function getCode(address beacon) internal pure returns (bytes memory) {
        return abi.encodePacked("`E\x80`\t=9=\xf3c\\`\xda\x1b=R===6==6==` =`\x04`\x1cs", beacon, "Z\xfa`2W\xfd[Q\x927Z\xf4=\x82\x80>\x90=\x91`CW\xfd[\xf3");
    }
}

library MinProxy {
    function proxyCode(address impl) internal pure returns (bytes memory) {
        return MinProxyGetCode.getCode(impl);
    }

    function beaconProxyCode(address beacon) internal pure returns (bytes memory) {
        return MinBeaconProxyGetCode.getCode(beacon);
    }

    function createProxy(address impl) internal returns (address) {
        return _create(proxyCode(impl));
    }

    function createBeaconProxy(address beacon) internal returns (address) {
        return _create(beaconProxyCode(beacon));
    }

    function _create(bytes memory code) private returns (address deployed) {
        assembly {
            deployed := create(0, add(code, 0x20), mload(code))
        }
        require(deployed != address(0), "MinProxy/zeroAddress: create failed");
    }
}

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

contract MaplestoryCharacter is
    ERC2771Context,
    ERC721("MaplestoryCharacter", "MSC"),
    ERC721Pausable,
    NextOwnablePausable,
    ApproveControlled,
    ERC721ApproveControlled {
    using Strings for uint256;

    string private _defaultBaseURI;
    uint256 private _totalSupply;
    MaplestoryCharacterInventoryImpl private immutable _impl;
    mapping(uint256 => string) private _characterBaseURIs;

    event DefaultBaseURIChanged(string previousURI, string newURI);
    event CharacterBaseURIChanged(uint256 indexed characterId, string previousURI, string newURI);
    event ItemDeposited(
        address indexed from,
        uint256 indexed characterId,
        address tokenAddress,
        uint256 indexed tokenId
    );
    event ItemWithdrawn(uint256 indexed characterId, address indexed to, address tokenAddress, uint256 indexed tokenId);
    event RetrievedCharacter(address from, address to, uint256 tokenId, string reason);

    modifier onlyCharacterOwner(address userWallet, uint256 characterId) {
        require(
            ERC721.ownerOf(characterId) == userWallet,
            "MaplestoryCharacter/wrongRequester: requester is not the character owner"
        );
        _;
    }

    constructor(
        address trustedForwarder_,
        ApproveController controller_,
        string memory defaultBaseURI_
    ) ERC2771Context(trustedForwarder_) ApproveControlled(controller_) {
        _defaultBaseURI = defaultBaseURI_;
        _impl = new MaplestoryCharacterInventoryImpl(MaplestoryCharacter(address(this)));
    }

    /// @notice Transfer ERC721 token to character.
    /// @param  userWallet owns the character.
    /// @param  characterId is new owner of token.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to character.
    function depositItemFromSender(
        address userWallet,
        uint256 characterId,
        IERC721 tokenAddress,
        uint256 tokenId
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        _depositItemFromSender(characterId, tokenAddress, tokenId);
    }

    /// @notice Batch function of {depositItemFromSender}.
    function depositBatchItemsFromSender(
        address userWallet,
        uint256 characterId,
        IERC721 tokenAddress,
        uint256[] memory tokenIds
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        uint256 tokensLength = tokenIds.length;
        for (uint256 i; i < tokensLength; ) {
            _depositItemFromSender(characterId, tokenAddress, tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Transfer ERC721 token to character.
    /// @dev    The ERC721 token's owner is userWallet.
    /// @param  userWallet owns the character.
    /// @param  characterId is new owner of token.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to character.
    function depositItemFromOwner(
        address userWallet,
        uint256 characterId,
        IERC721 tokenAddress,
        uint256 tokenId
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        _depositItemFromOwner(userWallet, characterId, tokenAddress, tokenId);
    }

    /// @notice Batch function of {depositItemFromOwner}.
    function depositBatchItemsFromOwner(
        address userWallet,
        uint256 characterId,
        IERC721 tokenAddress,
        uint256[] memory tokenIds
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        uint256 tokensLength = tokenIds.length;
        for (uint256 i; i < tokensLength; ) {
            _depositItemFromOwner(userWallet, characterId, tokenAddress, tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Transfer ERC721 token from character to `to` address.
    /// @param  characterId owns the token.
    /// @param  userWallet owns the character.
    /// @param  to receive the token from character.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to character.
    function withdrawItemTo(
        uint256 characterId,
        address userWallet,
        address to,
        IERC721 tokenAddress,
        uint256 tokenId
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        _withdrawItemTo(characterId, to, tokenAddress, tokenId);
    }

    /// @notice Batch function of {withdrawItemTo}.
    function withdrawBatchItemsTo(
        uint256 characterId,
        address userWallet,
        address to,
        IERC721 tokenAddress,
        uint256[] memory tokenIds
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        uint256 tokensLength = tokenIds.length;
        for (uint256 i; i < tokensLength; ) {
            _withdrawItemTo(characterId, to, tokenAddress, tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Transfer ERC721 token from character to user wallet.
    /// @param  characterId owns the token.
    /// @param  userWallet owns the character.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to user wallet.
    function withdrawItemToOwner(
        uint256 characterId,
        address userWallet,
        IERC721 tokenAddress,
        uint256 tokenId
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        _withdrawItemToOwner(characterId, tokenAddress, tokenId);
    }

    /// @notice Batch function of {withdrawItemToOwner}.
    function withdrawBatchItemsToOwner(
        uint256 characterId,
        address userWallet,
        IERC721 tokenAddress,
        uint256[] memory tokenIds
    ) external whenExecutable onlyCharacterOwner(userWallet, characterId) {
        uint256 tokensLength = tokenIds.length;
        for (uint256 i; i < tokensLength; ) {
            _withdrawItemToOwner(characterId, tokenAddress, tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Mints new MaplestoryCharacter token.
    /// @param  to Address to receive token.
    function mint(address to) external whenExecutable {
        _mint(to);
    }

    /// @notice Batch function of {Mint}.
    function mintBatch(address to, uint256 size) external whenExecutable {
        for (uint256 i; i < size; ) {
            _mint(to);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Set `_characterBaseURIs`.
    /// @param  characterId token's id.
    /// @param  newURI String of the new character's base uri.
    function setCharacterURI(uint256 characterId, string memory newURI) external whenExecutable {
        string memory previousURI = _characterBaseURIs[characterId];
        _characterBaseURIs[characterId] = newURI;
        emit CharacterBaseURIChanged(characterId, previousURI, newURI);
    }

    /// @notice Set `_defaultBaseURI`.
    /// @param  newDefaultBaseURI String of the new `_defaultBaseURI`.
    function setBaseURI(string memory newDefaultBaseURI) external whenExecutable {
        string memory previousURI = _defaultBaseURI;
        _defaultBaseURI = newDefaultBaseURI;
        emit DefaultBaseURIChanged(previousURI, _defaultBaseURI);
    }

    /// @notice Retrieve character by owner.
    /// @param  from Address of the character owner.
    /// @param  to Address of the character receiver.
    /// @param  tokenId Token's id.
    /// @param  reason Reason of the retrieval.
    function retrieveCharacter(address from, address to, uint256 tokenId, string memory reason) external onlyOwner {
        safeTransferFrom(from, to, tokenId, "");
        emit RetrievedCharacter(from, to, tokenId, reason);
    }

    /// @notice Returns whether the character minted.
    /// @param characterId token's id.
    /// @return bool Whether the character is minted.
    function exists(uint256 characterId) external view returns (bool) {
        return ERC721._exists(characterId);
    }

    /// @notice Returns `_totalSupply`.
    /// @return uint256 Number of `_totalSupply`.
    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    /// @notice Returns list of the tokens owner.
    /// @param  characterIds List of the token ids.
    /// @return Address list of the tokens owner.
    function ownerOfBatch(uint256[] memory characterIds) external view returns (address[] memory) {
        uint256 charactersLength = characterIds.length;
        address[] memory batchOwners = new address[](charactersLength);

        for (uint256 i; i < charactersLength; ++i) {
            batchOwners[i] = ownerOf(characterIds[i]);
        }

        return batchOwners;
    }

    /// @notice Returns token owner.
    /// @param  tokenId Token's id.
    /// @return Address of the token's current owner.
    function ownerOf(uint256 tokenId) public view virtual override returns (address) {
        address owner = _ownerOf(tokenId);
        if (owner == address(0)) {
            // nx-errors-ignore
            revert(
                string(
                    abi.encodePacked(
                        "MaplestoryCharacter/ownerOfInvalidID: invalid token ID(",
                        tokenId.toHexString(20),
                        ")"
                    )
                )
            );
        }
        return owner;
    }

    /// @notice Returns token's uri.
    /// @dev    Returns `_characterBaseURIs` if the base uri of character is set. Otherwise returns `_defaultBaseURI`.
    /// @param  characterId Token's id.
    /// @return String of the token uri.
    function tokenURI(uint256 characterId) public view override returns (string memory) {
        require(_exists(characterId), "MaplestoryCharacter/uriInvalidID: URI query for nonexistent character");
        string memory uri = bytes(_characterBaseURIs[characterId]).length > 0
            ? _characterBaseURIs[characterId]
            : _defaultBaseURI;

        return string(abi.encodePacked(uri, characterId.toHexString(20), ".json"));
    }

    /// @notice Hook called before any token transferred to ensure that the transfer is valid.
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 tokenId,
        uint256 batchSize
    ) internal override(ERC721, ERC721Pausable) {
        require(uint256(uint160(to)) != tokenId, "MaplestoryCharacter/transferInvalidID: transfer character to itself");
        ERC721Pausable._beforeTokenTransfer(from, to, tokenId, batchSize);
    }

    /// @notice Mints new MaplestoryCharacter token.
    /// @param  to Address to receive minted token.
    function _mint(address to) private {
        uint256 newCharacter = uint256(uint160(MinProxy.createProxy(address(_impl))));
        _totalSupply++;
        ERC721._safeMint(to, newCharacter);
    }

    /// @notice Transfer ERC721 token to character.
    /// @dev    The ERC721 token's owner is msg sender.
    /// @param  characterId receive token.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to character.
    function _depositItemFromSender(uint256 characterId, IERC721 tokenAddress, uint256 tokenId) private {
        tokenAddress.safeTransferFrom(_msgSender(), address(uint160(characterId)), tokenId);
        emit ItemDeposited(_msgSender(), characterId, address(tokenAddress), tokenId);
    }

    /// @notice Transfer ERC721 token to character.
    /// @dev    The ERC721 token's owner is userWallet.
    /// @param  userWallet owns the character.
    /// @param  characterId receive token.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to character.
    function _depositItemFromOwner(
        address userWallet,
        uint256 characterId,
        IERC721 tokenAddress,
        uint256 tokenId
    ) private {
        tokenAddress.safeTransferFrom(userWallet, address(uint160(characterId)), tokenId);
        emit ItemDeposited(userWallet, characterId, address(tokenAddress), tokenId);
    }

    /// @notice Transfer ERC721 token from character to character's owner wallet.
    /// @param  characterId owns the token.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to user wallet.
    function _withdrawItemToOwner(uint256 characterId, IERC721 tokenAddress, uint256 tokenId) private {
        _withdrawItemTo(characterId, ERC721.ownerOf(characterId), tokenAddress, tokenId);
    }

    /// @notice Transfer ERC721 token from character to `to` address.
    /// @param  characterId owns the token.
    /// @param  to receive the token from character.
    /// @param  tokenAddress transferred token's contract address.
    /// @param  tokenId transferred to user wallet.
    function _withdrawItemTo(uint256 characterId, address to, IERC721 tokenAddress, uint256 tokenId) private {
        MaplestoryCharacterInventoryImpl(address(uint160(characterId))).withdrawItem(to, tokenAddress, tokenId);
        emit ItemWithdrawn(characterId, to, address(tokenAddress), tokenId);
    }

    /* trivial overrides */

    /// @notice See {ERC721ApproveControlled-isApprovedForAll}.
    function isApprovedForAll(
        address owner_,
        address operator_
    ) public view override(ERC721, ERC721ApproveControlled) returns (bool) {
        if (owner() == _msgSender()) {
            return true;
        }
        return ERC721ApproveControlled.isApprovedForAll(owner_, operator_);
    }

    /// @notice See {ERC721ApproveControlled-_approve}.
    function _approve(address to, uint256 tokenId) internal virtual override(ERC721, ERC721ApproveControlled) {
        ERC721ApproveControlled._approve(to, tokenId);
    }

    /// @notice See {ERC721ApproveControlled-_setApprovalForAll}.
    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual override(ERC721, ERC721ApproveControlled) {
        ERC721ApproveControlled._setApprovalForAll(owner, operator, approved);
    }

    /// @notice See {ERC2771Context-_msgSender}.
    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    /// @notice See {ERC2771Context-_msgData}.
    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}

contract MaplestoryCharacterInventoryImpl is Context, ERC721Holder {
    MaplestoryCharacter private immutable _character;

    constructor(MaplestoryCharacter character) {
        _character = character;
    }

    /// @notice Transfer ERC721 token from character to `to` address.
    /// @param to Receive the token from character.
    /// @param tokenAddress Transferred token's contract address.
    /// @param tokenId Token's id.
    function withdrawItem(address to, IERC721 tokenAddress, uint256 tokenId) external {
        // solhint-disable-next-line reason-string
        require(
            _msgSender() == address(_character),
            "MaplestoryInventory/withdrawForbidden: caller is not the character token contract"
        );
        tokenAddress.transferFrom(address(this), to, tokenId);
    }
}


/// @title Collection
/// @notice Items acquired in the game can be placed in a collection to give them additional stats in MapleStoryN(game).
/// Items can be collected from a wallet or character to a collection, and vice versa. A collection is mapped to
/// a wallet address, so a wallet can have a single collection, and a collection extends to all characters in the wallet.
/// Collected items can also be extracted to any character in the wallet.
contract Collection is ERC2771Context, NextOwnablePausable {
    using SafeERC20 for IERC20;

    struct SlotInfo {
        uint256 nftTokenId;
        uint64 itemId;
        bool valid;
    }

    struct TokenInfo {
        uint256 nftTokenId;
        string slotKey;
    }

    /// @notice CA of MaplestoryEquip
    MaplestoryEquip public immutable equipContract;
    /// @notice CA of MaplestoryCharacter
    MaplestoryCharacter public immutable characterContract;

    mapping(address => mapping(string => SlotInfo)) private _slotInfo;

    /// @notice Emitted when item added into collection from user wallet
    /// @param userWallet EOA of user
    /// @param itemId Item id
    /// @param tokenId Token id
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    event ItemAdded(address indexed userWallet, uint64 indexed itemId, uint256 indexed tokenId, string slotKey);
    /// @notice Emitted when item added into collection from character
    /// @param tokenOwner The owner of token, same as user wallet
    /// @param charId Character id
    /// @param itemId Item id
    /// @param tokenId Token id
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    event ItemAddedByChar(
        address indexed tokenOwner,
        uint256 charId,
        uint64 indexed itemId,
        uint256 indexed tokenId,
        string slotKey
    );
    /// @notice Emitted when item returned to user wallet
    /// @param userWallet EOA of user
    /// @param itemId Item id
    /// @param tokenId Token id
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    event ItemReturned(address indexed userWallet, uint64 indexed itemId, uint256 indexed tokenId, string slotKey);
    /// @notice Emitted when item returned to character
    /// @param tokenOwner The owner of token, same as user wallet
    /// @param charId Character id
    /// @param itemId Item id
    /// @param tokenId Token id
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    event ItemReturnedByChar(
        address indexed tokenOwner,
        uint256 charId,
        uint64 indexed itemId,
        uint256 indexed tokenId,
        string slotKey
    );
    /// @notice Emitted when clear item slot to empty
    /// @param account EOA of user
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    event SlotCleared(address indexed account, string slotKey);

    modifier validAddress(address addr) {
        require(addr != address(0), "Collection/validAddress: couldn't be zero address");
        _;
    }

    /// @dev Need CAs for deploy this contract
    /// @param equipContract_ CA of the MaplestoryEquip
    /// @param characterContract_ CA of the MaplestoryCharacter
    constructor(
        address trustedForwarder_,
        MaplestoryEquip equipContract_,
        MaplestoryCharacter characterContract_
    )
        ERC2771Context(trustedForwarder_)
        validAddress(address(equipContract_))
        validAddress(address(characterContract_))
    {
        equipContract = equipContract_;
        characterContract = characterContract_;
        equipContract.setApprovalForAll(address(characterContract), true);
    }

    /// @notice Function for adding a item from user to collection
    /// @param userWallet The address of the user who owns the item to be added to the collection
    /// @param tokenInfo Information of the token that to be enrolled in the collection
    function addItem(
        address userWallet,
        TokenInfo calldata tokenInfo
    ) external validAddress(userWallet) whenExecutable {
        _addItem(userWallet, tokenInfo.nftTokenId, tokenInfo.slotKey);
    }

    /// @notice Function for adding items from user to collection
    /// @param userWallet The address of the user who owns the item to be added to the collection
    /// @param tokenInfoList Information of the tokens that to be enrolled in the collection
    function addBatchItem(
        address userWallet,
        TokenInfo[] calldata tokenInfoList
    ) external validAddress(userWallet) whenExecutable {
        uint256 tLen = tokenInfoList.length;

        for (uint256 i; i < tLen; ) {
            _addItem(userWallet, tokenInfoList[i].nftTokenId, tokenInfoList[i].slotKey);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Function for returning a item from collection to user
    /// @param userWallet The address of the user who receives the added item in the collection
    /// @param tokenInfo Information of the token that to be enrolled in the collection
    function returnItem(
        address userWallet,
        TokenInfo calldata tokenInfo
    ) external validAddress(userWallet) whenExecutable {
        _returnItem(userWallet, tokenInfo.nftTokenId, tokenInfo.slotKey);
    }

    /// @notice Function for returning items from collection to user
    /// @param userWallet The address of the user who receives the added item in the collection
    /// @param tokenInfoList Information of the tokens that to be enrolled in the collection
    function returnBatchItem(
        address userWallet,
        TokenInfo[] calldata tokenInfoList
    ) external validAddress(userWallet) whenExecutable {
        uint256 tLen = tokenInfoList.length;

        for (uint256 i; i < tLen; ) {
            _returnItem(userWallet, tokenInfoList[i].nftTokenId, tokenInfoList[i].slotKey);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Function for adding a item from character to collection
    /// @param charId The character id for sending the item
    /// @param userWallet The address of the user who owns the item to be added to the collection
    /// @param tokenInfo Information of the token that to be enrolled in the collection
    function addItemByChar(
        uint256 charId,
        address userWallet,
        TokenInfo calldata tokenInfo
    ) external validAddress(userWallet) whenExecutable {
        _addItemByChar(charId, userWallet, tokenInfo.nftTokenId, tokenInfo.slotKey);
    }

    /// @notice Function for adding a item from character to collection
    /// @param charId The character id for sending the item
    /// @param userWallet The address of the user who owns the item to be added to the collection
    /// @param tokenInfoList Information of the tokens that to be enrolled in the collection
    function addBatchItemByChar(
        uint256 charId,
        address userWallet,
        TokenInfo[] calldata tokenInfoList
    ) external validAddress(userWallet) whenExecutable {
        uint256 tLen = tokenInfoList.length;

        for (uint256 i; i < tLen; ) {
            _addItemByChar(charId, userWallet, tokenInfoList[i].nftTokenId, tokenInfoList[i].slotKey);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Function for returning a item from collection to character
    /// @param charId The character id for receiving the item
    /// @param userWallet The address of the user who receives the added item in the collection
    /// @param tokenInfo Information of the token that to be enrolled in the collection
    function returnItemByChar(
        uint256 charId,
        address userWallet,
        TokenInfo calldata tokenInfo
    ) external validAddress(userWallet) whenExecutable {
        _returnItemByChar(charId, userWallet, tokenInfo.nftTokenId, tokenInfo.slotKey);
    }

    /// @notice Function for returning items from collection to character
    /// @param charId The character id for receiving the item
    /// @param userWallet The address of the user who receives the added item in the collection
    /// @param tokenInfoList Information of the tokens that to be enrolled in the collection
    function returnBatchItemByChar(
        uint256 charId,
        address userWallet,
        TokenInfo[] calldata tokenInfoList
    ) external validAddress(userWallet) whenExecutable {
        uint256 tLen = tokenInfoList.length;

        for (uint256 i; i < tLen; ) {
            _returnItemByChar(charId, userWallet, tokenInfoList[i].nftTokenId, tokenInfoList[i].slotKey);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Clear slot information; This function is a contingency and is not normally used
    /// @param account EOA of user
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    function clearSlot(address account, string calldata slotKey) external onlyOwner {
        require(_slotInfo[account][slotKey].valid, "Collection/slotEmpty: slot is empty");
        _slotInfo[account][slotKey].valid = false;
        emit SlotCleared(account, slotKey);
    }

    /// @notice Withdraw ERC-20 base tokens; This function is a contingency and is not normally used
    /// @param token CA of be withdrawing token
    /// @param tos Address of receiving the token
    /// @param amounts Amounts for withdraw
    function withdrawERC20(IERC20 token, address[] calldata tos, uint256[] calldata amounts) external onlyOwner {
        require(tos.length == amounts.length, "Collection/mismatch: tos and amounts length mismatch");
        uint256 len = tos.length;
        for (uint256 i; i < len; ) {
            token.safeTransfer(tos[i], amounts[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Withdraw ERC-721 base tokens; This function is a contingency and is not normally used
    /// @param token CA of be withdrawing token
    /// @param tos Addresses of receiving the token
    /// @param tokenIds Token ids for withdraw
    function withdrawERC721(IERC721 token, address[] calldata tos, uint256[] calldata tokenIds) external onlyOwner {
        require(tos.length == tokenIds.length, "Collection/mismatch: tos and tokenIds length mismatch");
        uint256 len = tos.length;
        for (uint256 i; i < len; ) {
            token.safeTransferFrom(address(this), tos[i], tokenIds[i]);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Retrieve slot information by `account` and `slotKey`
    /// @param account EOA of user
    /// @param slotKey The unique ID of the slot where the item is registered in the collection
    /// @return SlotInfo The slot information; see {Collection-SlotInfo}
    function slotInfo(address account, string calldata slotKey) external view returns (SlotInfo memory) {
        return _slotInfo[account][slotKey];
    }

    function _addItem(address userWallet, uint256 nftTokenId, string memory slotKey) internal {
        uint64 itemId = _tokenItemId(nftTokenId);
        require(!_slotInfo[userWallet][slotKey].valid, "Collection/slotOccupied: slot is occupied");

        _slotInfo[userWallet][slotKey] = SlotInfo(nftTokenId, itemId, true);

        equipContract.transferFrom(userWallet, address(this), nftTokenId);
        emit ItemAdded(userWallet, itemId, nftTokenId, slotKey);
    }

    function _returnItem(address userWallet, uint256 nftTokenId, string memory slotKey) internal {
        uint64 itemId = _tokenItemId(nftTokenId);
        require(_slotInfo[userWallet][slotKey].valid, "Collection/slotEmpty: slot is empty");
        require(
            _slotInfo[userWallet][slotKey].nftTokenId == nftTokenId,
            "Collection/slotConflict: requested token is not the stored one"
        );

        _slotInfo[userWallet][slotKey].valid = false;

        equipContract.transferFrom(address(this), userWallet, nftTokenId);
        emit ItemReturned(userWallet, itemId, nftTokenId, slotKey);
    }

    function _addItemByChar(uint256 charId, address userWallet, uint256 nftTokenId, string memory slotKey) internal {
        uint64 itemId = _tokenItemId(nftTokenId);
        require(!_slotInfo[userWallet][slotKey].valid, "Collection/slotOccupied: slot is occupied");
        require(characterContract.ownerOf(charId) == userWallet, "Collection/invalidID: wrong charId");

        _slotInfo[userWallet][slotKey] = SlotInfo(nftTokenId, itemId, true);

        characterContract.withdrawItemTo(charId, userWallet, address(this), equipContract, nftTokenId);
        emit ItemAddedByChar(userWallet, charId, itemId, nftTokenId, slotKey);
    }

    function _returnItemByChar(uint256 charId, address userWallet, uint256 nftTokenId, string memory slotKey) internal {
        uint64 itemId = _tokenItemId(nftTokenId);
        require(_slotInfo[userWallet][slotKey].valid, "Collection/slotEmpty: slot is empty");
        require(
            _slotInfo[userWallet][slotKey].nftTokenId == nftTokenId,
            "Collection/slotConflict: requested token is not the stored one"
        );

        _slotInfo[userWallet][slotKey].valid = false;

        characterContract.depositItemFromSender(userWallet, charId, equipContract, nftTokenId);
        emit ItemReturnedByChar(userWallet, charId, itemId, nftTokenId, slotKey);
    }

    function _tokenItemId(uint256 nftTokenId) internal view returns (uint64) {
        return equipContract.tokenItemId(nftTokenId);
    }

    /* trivial overrides */
    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}