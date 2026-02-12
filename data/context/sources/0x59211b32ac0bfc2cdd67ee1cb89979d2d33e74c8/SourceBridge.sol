

// Sources flattened with hardhat v2.22.6 https://hardhat.org

// SPDX-License-Identifier: Ecosystem AND MIT

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


// File @openzeppelin/contracts/token/ERC1155/IERC1155.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.7.0) (token/ERC1155/IERC1155.sol)

pragma solidity ^0.8.0;

/**
 * @dev Required interface of an ERC1155 compliant contract, as defined in the
 * https://eips.ethereum.org/EIPS/eip-1155[EIP].
 *
 * _Available since v3.1._
 */
interface IERC1155 is IERC165 {
    /**
     * @dev Emitted when `value` tokens of token type `id` are transferred from `from` to `to` by `operator`.
     */
    event TransferSingle(address indexed operator, address indexed from, address indexed to, uint256 id, uint256 value);

    /**
     * @dev Equivalent to multiple {TransferSingle} events, where `operator`, `from` and `to` are the same for all
     * transfers.
     */
    event TransferBatch(
        address indexed operator,
        address indexed from,
        address indexed to,
        uint256[] ids,
        uint256[] values
    );

    /**
     * @dev Emitted when `account` grants or revokes permission to `operator` to transfer their tokens, according to
     * `approved`.
     */
    event ApprovalForAll(address indexed account, address indexed operator, bool approved);

    /**
     * @dev Emitted when the URI for token type `id` changes to `value`, if it is a non-programmatic URI.
     *
     * If an {URI} event was emitted for `id`, the standard
     * https://eips.ethereum.org/EIPS/eip-1155#metadata-extensions[guarantees] that `value` will equal the value
     * returned by {IERC1155MetadataURI-uri}.
     */
    event URI(string value, uint256 indexed id);

    /**
     * @dev Returns the amount of tokens of token type `id` owned by `account`.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function balanceOf(address account, uint256 id) external view returns (uint256);

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {balanceOf}.
     *
     * Requirements:
     *
     * - `accounts` and `ids` must have the same length.
     */
    function balanceOfBatch(address[] calldata accounts, uint256[] calldata ids)
        external
        view
        returns (uint256[] memory);

    /**
     * @dev Grants or revokes permission to `operator` to transfer the caller's tokens, according to `approved`,
     *
     * Emits an {ApprovalForAll} event.
     *
     * Requirements:
     *
     * - `operator` cannot be the caller.
     */
    function setApprovalForAll(address operator, bool approved) external;

    /**
     * @dev Returns true if `operator` is approved to transfer ``account``'s tokens.
     *
     * See {setApprovalForAll}.
     */
    function isApprovedForAll(address account, address operator) external view returns (bool);

    /**
     * @dev Transfers `amount` tokens of token type `id` from `from` to `to`.
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - If the caller is not `from`, it must have been approved to spend ``from``'s tokens via {setApprovalForAll}.
     * - `from` must have a balance of tokens of type `id` of at least `amount`.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155Received} and return the
     * acceptance magic value.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes calldata data
    ) external;

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {safeTransferFrom}.
     *
     * Emits a {TransferBatch} event.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155BatchReceived} and return the
     * acceptance magic value.
     */
    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] calldata ids,
        uint256[] calldata amounts,
        bytes calldata data
    ) external;
}


// File @openzeppelin/contracts/token/ERC1155/extensions/IERC1155MetadataURI.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC1155/extensions/IERC1155MetadataURI.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the optional ERC1155MetadataExtension interface, as defined
 * in the https://eips.ethereum.org/EIPS/eip-1155#metadata-extensions[EIP].
 *
 * _Available since v3.1._
 */
interface IERC1155MetadataURI is IERC1155 {
    /**
     * @dev Returns the URI for token type `id`.
     *
     * If the `\{id\}` substring is present in the URI, it must be replaced by
     * clients with the actual token type ID.
     */
    function uri(uint256 id) external view returns (string memory);
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


// File @openzeppelin/contracts/token/ERC1155/ERC1155.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC1155/ERC1155.sol)

pragma solidity ^0.8.0;






/**
 * @dev Implementation of the basic standard multi-token.
 * See https://eips.ethereum.org/EIPS/eip-1155
 * Originally based on code by Enjin: https://github.com/enjin/erc-1155
 *
 * _Available since v3.1._
 */
contract ERC1155 is Context, ERC165, IERC1155, IERC1155MetadataURI {
    using Address for address;

    // Mapping from token ID to account balances
    mapping(uint256 => mapping(address => uint256)) private _balances;

    // Mapping from account to operator approvals
    mapping(address => mapping(address => bool)) private _operatorApprovals;

    // Used as the URI for all token types by relying on ID substitution, e.g. https://token-cdn-domain/{id}.json
    string private _uri;

    /**
     * @dev See {_setURI}.
     */
    constructor(string memory uri_) {
        _setURI(uri_);
    }

    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override(ERC165, IERC165) returns (bool) {
        return
            interfaceId == type(IERC1155).interfaceId ||
            interfaceId == type(IERC1155MetadataURI).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    /**
     * @dev See {IERC1155MetadataURI-uri}.
     *
     * This implementation returns the same URI for *all* token types. It relies
     * on the token type ID substitution mechanism
     * https://eips.ethereum.org/EIPS/eip-1155#metadata[defined in the EIP].
     *
     * Clients calling this function must replace the `\{id\}` substring with the
     * actual token type ID.
     */
    function uri(uint256) public view virtual override returns (string memory) {
        return _uri;
    }

    /**
     * @dev See {IERC1155-balanceOf}.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function balanceOf(address account, uint256 id) public view virtual override returns (uint256) {
        require(account != address(0), "ERC1155: address zero is not a valid owner");
        return _balances[id][account];
    }

    /**
     * @dev See {IERC1155-balanceOfBatch}.
     *
     * Requirements:
     *
     * - `accounts` and `ids` must have the same length.
     */
    function balanceOfBatch(address[] memory accounts, uint256[] memory ids)
        public
        view
        virtual
        override
        returns (uint256[] memory)
    {
        require(accounts.length == ids.length, "ERC1155: accounts and ids length mismatch");

        uint256[] memory batchBalances = new uint256[](accounts.length);

        for (uint256 i = 0; i < accounts.length; ++i) {
            batchBalances[i] = balanceOf(accounts[i], ids[i]);
        }

        return batchBalances;
    }

    /**
     * @dev See {IERC1155-setApprovalForAll}.
     */
    function setApprovalForAll(address operator, bool approved) public virtual override {
        _setApprovalForAll(_msgSender(), operator, approved);
    }

    /**
     * @dev See {IERC1155-isApprovedForAll}.
     */
    function isApprovedForAll(address account, address operator) public view virtual override returns (bool) {
        return _operatorApprovals[account][operator];
    }

    /**
     * @dev See {IERC1155-safeTransferFrom}.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    ) public virtual override {
        require(
            from == _msgSender() || isApprovedForAll(from, _msgSender()),
            "ERC1155: caller is not token owner or approved"
        );
        _safeTransferFrom(from, to, id, amount, data);
    }

    /**
     * @dev See {IERC1155-safeBatchTransferFrom}.
     */
    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) public virtual override {
        require(
            from == _msgSender() || isApprovedForAll(from, _msgSender()),
            "ERC1155: caller is not token owner or approved"
        );
        _safeBatchTransferFrom(from, to, ids, amounts, data);
    }

    /**
     * @dev Transfers `amount` tokens of token type `id` from `from` to `to`.
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - `from` must have a balance of tokens of type `id` of at least `amount`.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155Received} and return the
     * acceptance magic value.
     */
    function _safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    ) internal virtual {
        require(to != address(0), "ERC1155: transfer to the zero address");

        address operator = _msgSender();
        uint256[] memory ids = _asSingletonArray(id);
        uint256[] memory amounts = _asSingletonArray(amount);

        _beforeTokenTransfer(operator, from, to, ids, amounts, data);

        uint256 fromBalance = _balances[id][from];
        require(fromBalance >= amount, "ERC1155: insufficient balance for transfer");
        unchecked {
            _balances[id][from] = fromBalance - amount;
        }
        _balances[id][to] += amount;

        emit TransferSingle(operator, from, to, id, amount);

        _afterTokenTransfer(operator, from, to, ids, amounts, data);

        _doSafeTransferAcceptanceCheck(operator, from, to, id, amount, data);
    }

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {_safeTransferFrom}.
     *
     * Emits a {TransferBatch} event.
     *
     * Requirements:
     *
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155BatchReceived} and return the
     * acceptance magic value.
     */
    function _safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) internal virtual {
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");
        require(to != address(0), "ERC1155: transfer to the zero address");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, from, to, ids, amounts, data);

        for (uint256 i = 0; i < ids.length; ++i) {
            uint256 id = ids[i];
            uint256 amount = amounts[i];

            uint256 fromBalance = _balances[id][from];
            require(fromBalance >= amount, "ERC1155: insufficient balance for transfer");
            unchecked {
                _balances[id][from] = fromBalance - amount;
            }
            _balances[id][to] += amount;
        }

        emit TransferBatch(operator, from, to, ids, amounts);

        _afterTokenTransfer(operator, from, to, ids, amounts, data);

        _doSafeBatchTransferAcceptanceCheck(operator, from, to, ids, amounts, data);
    }

    /**
     * @dev Sets a new URI for all token types, by relying on the token type ID
     * substitution mechanism
     * https://eips.ethereum.org/EIPS/eip-1155#metadata[defined in the EIP].
     *
     * By this mechanism, any occurrence of the `\{id\}` substring in either the
     * URI or any of the amounts in the JSON file at said URI will be replaced by
     * clients with the token type ID.
     *
     * For example, the `https://token-cdn-domain/\{id\}.json` URI would be
     * interpreted by clients as
     * `https://token-cdn-domain/000000000000000000000000000000000000000000000000000000000004cce0.json`
     * for token type ID 0x4cce0.
     *
     * See {uri}.
     *
     * Because these URIs cannot be meaningfully represented by the {URI} event,
     * this function emits no events.
     */
    function _setURI(string memory newuri) internal virtual {
        _uri = newuri;
    }

    /**
     * @dev Creates `amount` tokens of token type `id`, and assigns them to `to`.
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155Received} and return the
     * acceptance magic value.
     */
    function _mint(
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    ) internal virtual {
        require(to != address(0), "ERC1155: mint to the zero address");

        address operator = _msgSender();
        uint256[] memory ids = _asSingletonArray(id);
        uint256[] memory amounts = _asSingletonArray(amount);

        _beforeTokenTransfer(operator, address(0), to, ids, amounts, data);

        _balances[id][to] += amount;
        emit TransferSingle(operator, address(0), to, id, amount);

        _afterTokenTransfer(operator, address(0), to, ids, amounts, data);

        _doSafeTransferAcceptanceCheck(operator, address(0), to, id, amount, data);
    }

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {_mint}.
     *
     * Emits a {TransferBatch} event.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155BatchReceived} and return the
     * acceptance magic value.
     */
    function _mintBatch(
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) internal virtual {
        require(to != address(0), "ERC1155: mint to the zero address");
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, address(0), to, ids, amounts, data);

        for (uint256 i = 0; i < ids.length; i++) {
            _balances[ids[i]][to] += amounts[i];
        }

        emit TransferBatch(operator, address(0), to, ids, amounts);

        _afterTokenTransfer(operator, address(0), to, ids, amounts, data);

        _doSafeBatchTransferAcceptanceCheck(operator, address(0), to, ids, amounts, data);
    }

    /**
     * @dev Destroys `amount` tokens of token type `id` from `from`
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `from` must have at least `amount` tokens of token type `id`.
     */
    function _burn(
        address from,
        uint256 id,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC1155: burn from the zero address");

        address operator = _msgSender();
        uint256[] memory ids = _asSingletonArray(id);
        uint256[] memory amounts = _asSingletonArray(amount);

        _beforeTokenTransfer(operator, from, address(0), ids, amounts, "");

        uint256 fromBalance = _balances[id][from];
        require(fromBalance >= amount, "ERC1155: burn amount exceeds balance");
        unchecked {
            _balances[id][from] = fromBalance - amount;
        }

        emit TransferSingle(operator, from, address(0), id, amount);

        _afterTokenTransfer(operator, from, address(0), ids, amounts, "");
    }

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {_burn}.
     *
     * Emits a {TransferBatch} event.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     */
    function _burnBatch(
        address from,
        uint256[] memory ids,
        uint256[] memory amounts
    ) internal virtual {
        require(from != address(0), "ERC1155: burn from the zero address");
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, from, address(0), ids, amounts, "");

        for (uint256 i = 0; i < ids.length; i++) {
            uint256 id = ids[i];
            uint256 amount = amounts[i];

            uint256 fromBalance = _balances[id][from];
            require(fromBalance >= amount, "ERC1155: burn amount exceeds balance");
            unchecked {
                _balances[id][from] = fromBalance - amount;
            }
        }

        emit TransferBatch(operator, from, address(0), ids, amounts);

        _afterTokenTransfer(operator, from, address(0), ids, amounts, "");
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
        require(owner != operator, "ERC1155: setting approval status for self");
        _operatorApprovals[owner][operator] = approved;
        emit ApprovalForAll(owner, operator, approved);
    }

    /**
     * @dev Hook that is called before any token transfer. This includes minting
     * and burning, as well as batched variants.
     *
     * The same hook is called on both single and batched variants. For single
     * transfers, the length of the `ids` and `amounts` arrays will be 1.
     *
     * Calling conditions (for each `id` and `amount` pair):
     *
     * - When `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * of token type `id` will be  transferred to `to`.
     * - When `from` is zero, `amount` tokens of token type `id` will be minted
     * for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens of token type `id`
     * will be burned.
     * - `from` and `to` are never both zero.
     * - `ids` and `amounts` have the same, non-zero length.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address operator,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) internal virtual {}

    /**
     * @dev Hook that is called after any token transfer. This includes minting
     * and burning, as well as batched variants.
     *
     * The same hook is called on both single and batched variants. For single
     * transfers, the length of the `id` and `amount` arrays will be 1.
     *
     * Calling conditions (for each `id` and `amount` pair):
     *
     * - When `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * of token type `id` will be  transferred to `to`.
     * - When `from` is zero, `amount` tokens of token type `id` will be minted
     * for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens of token type `id`
     * will be burned.
     * - `from` and `to` are never both zero.
     * - `ids` and `amounts` have the same, non-zero length.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address operator,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) internal virtual {}

    function _doSafeTransferAcceptanceCheck(
        address operator,
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    ) private {
        if (to.isContract()) {
            try IERC1155Receiver(to).onERC1155Received(operator, from, id, amount, data) returns (bytes4 response) {
                if (response != IERC1155Receiver.onERC1155Received.selector) {
                    revert("ERC1155: ERC1155Receiver rejected tokens");
                }
            } catch Error(string memory reason) {
                revert(reason);
            } catch {
                revert("ERC1155: transfer to non-ERC1155Receiver implementer");
            }
        }
    }

    function _doSafeBatchTransferAcceptanceCheck(
        address operator,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    ) private {
        if (to.isContract()) {
            try IERC1155Receiver(to).onERC1155BatchReceived(operator, from, ids, amounts, data) returns (
                bytes4 response
            ) {
                if (response != IERC1155Receiver.onERC1155BatchReceived.selector) {
                    revert("ERC1155: ERC1155Receiver rejected tokens");
                }
            } catch Error(string memory reason) {
                revert(reason);
            } catch {
                revert("ERC1155: transfer to non-ERC1155Receiver implementer");
            }
        }
    }

    function _asSingletonArray(uint256 element) private pure returns (uint256[] memory) {
        uint256[] memory array = new uint256[](1);
        array[0] = element;

        return array;
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


// File @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


// File @openzeppelin/contracts/token/ERC20/ERC20.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/ERC20.sol)

pragma solidity ^0.8.0;



/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.openzeppelin.com/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC20
 * applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}
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


// File @openzeppelin/contracts/token/ERC721/IERC721.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC721/IERC721.sol)

pragma solidity ^0.8.0;

/**
 * @dev Required interface of an ERC721 compliant contract.
 */
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


// File @openzeppelin/contracts/token/ERC721/extensions/IERC721Metadata.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC721/extensions/IERC721Metadata.sol)

pragma solidity ^0.8.0;

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


// File @openzeppelin/contracts/utils/Strings.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/Strings.sol)

pragma solidity ^0.8.0;

/**
 * @dev String operations.
 */
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


// File @openzeppelin/contracts/token/ERC721/ERC721.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC721/ERC721.sol)

pragma solidity ^0.8.0;







/**
 * @dev Implementation of https://eips.ethereum.org/EIPS/eip-721[ERC721] Non-Fungible Token Standard, including
 * the Metadata extension, but not including the Enumerable extension, which is available separately as
 * {ERC721Enumerable}.
 */
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


// File @openzeppelin/contracts/security/ReentrancyGuard.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (security/ReentrancyGuard.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}


// File contracts/Bridge/libs/Teleporter/ITeleporterMessenger.sol

// (c) 2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: Ecosystem

pragma solidity 0.8.18;

// A message receipt identifies the message that was delivered by its nonce,
// and the address that can redeem the reward for that message.
struct TeleporterMessageReceipt {
    uint256 receivedMessageNonce;
    address relayerRewardAddress;
}

// Represents all of the information required for submitting a Teleporter message
// to be sent to the given destination chain ID and address. Includes the fee
// information for the message, the amount of gas the relayer must provide to execute
// the message on the destination chain, the relayer accounts allowed to deliver the
// message, and the message data itself.
struct TeleporterMessageInput {
    bytes32 destinationBlockchainID;
    address destinationAddress;
    TeleporterFeeInfo feeInfo;
    uint256 requiredGasLimit;
    address[] allowedRelayerAddresses;
    bytes message;
}

// Represents a message sent or received by an implementation of {ITeleporterMessenger}.
struct TeleporterMessage {
    uint256 messageNonce;
    address originSenderAddress;
    bytes32 destinationBlockchainID;
    address destinationAddress;
    uint256 requiredGasLimit;
    address[] allowedRelayerAddresses;
    TeleporterMessageReceipt[] receipts;
    bytes message;
}

// Represents the fee information associated to a given Teleporter message.
// The contract address is the asset contract the fee will be paid in, and
// the amount is the amount of that specified asset.
struct TeleporterFeeInfo {
    address feeTokenAddress;
    uint256 amount;
}

/**
 * @dev Interface that describes functionalities for a cross-chain messenger implementing the Teleporter protcol.
 *
 * @custom:security-contact https://github.com/ava-labs/teleporter/blob/main/SECURITY.md
 */
interface ITeleporterMessenger {
    /**
     * @notice Emitted when the blockchain ID of the contract instance is initialized using the Warp precompile.
     */
    event BlockchainIDInitialized(bytes32 indexed blockchainID);

    /**
     * @notice Emitted when sending a Teleporter message cross-chain.
     */
    event SendCrossChainMessage(
        bytes32 indexed messageID,
        bytes32 indexed destinationBlockchainID,
        TeleporterMessage message,
        TeleporterFeeInfo feeInfo
    );

    /**
     * @notice Emitted when an additional fee amount is added to a Teleporter message that had previously
     * been sent, but not yet delivered to the destination chain.
     */
    event AddFeeAmount(bytes32 indexed messageID, TeleporterFeeInfo updatedFeeInfo);

    /**
     * @notice Emitted when a Teleporter message is being delivered on the destination chain to an address,
     * but message execution fails. Failed messages can then be retried with `retryMessageExecution`
     */
    event MessageExecutionFailed(
        bytes32 indexed messageID,
        bytes32 indexed sourceBlockchainID,
        TeleporterMessage message
    );

    /**
     * @notice Emitted when a Teleporter message is successfully executed with the
     * specified destination address and message call data. This can occur either when
     * the message is initially received, or on a retry attempt.
     *
     * Each message received can be executed successfully at most once.
     */
    event MessageExecuted(bytes32 indexed messageID, bytes32 indexed sourceBlockchainID);

    /**
     * @notice Emitted when a TeleporterMessage is successfully received.
     */
    event ReceiveCrossChainMessage(
        bytes32 indexed messageID,
        bytes32 indexed sourceBlockchainID,
        address indexed deliverer,
        address rewardRedeemer,
        TeleporterMessage message
    );

    /**
     * @notice Emitted when a receipt is marked as received on the source chain that sent the
     * corresponding Teleporter message.
     */
    event ReceiptReceived(
        bytes32 indexed messageID,
        bytes32 indexed destinationBlockchainID,
        address indexed relayerRewardAddress,
        TeleporterFeeInfo feeInfo
    );

    /**
     * @notice Emitted when an account redeems accumulated relayer rewards.
     */
    event RelayerRewardsRedeemed(address indexed redeemer, address indexed asset, uint256 amount);

    /**
     * @notice Called by transactions to initiate the sending of a cross-chain message.
     * @return The message ID of the newly sent message.
     */
    function sendCrossChainMessage(TeleporterMessageInput calldata messageInput) external returns (bytes32);

    /**
     * @notice Called by transactions to retry the sending of a cross-chain message.
     *
     * @dev Retriggers the sending of a message previously emitted by sendCrossChainMessage that has not yet been acknowledged
     * with a receipt from the destination chain. This may be necessary in the unlikely event that less than the required
     * threshold of stake weight successfully inserted the message in their messages DB at the time of the first submission.
     * The message is checked to have already been previously submitted by comparing its message hash against those kept in
     * state until a receipt is received for the message.
     */
    function retrySendCrossChainMessage(TeleporterMessage calldata message) external;

    /**
     * @notice Adds the additional fee amount to the amount to be paid to the relayer that delivers
     * the given message ID to the destination chain.
     *
     * @dev The fee token address must be the same asset type as the fee asset specified in the original
     * call to sendCrossChainMessage. Reverts if the message doesn't exist or there is already
     * receipt of delivery of the message.
     */
    function addFeeAmount(bytes32 messageID, address feeTokenAddress, uint256 additionalFeeAmount) external;

    /**
     * @notice Receives a cross-chain message, and marks the `relayerRewardAddress` for fee reward for a successful delivery.
     *
     * @dev The message specified by `messageIndex` must be provided at that index in the access list storage slots of the transaction,
     * and is verified in the precompile predicate.
     */
    function receiveCrossChainMessage(uint32 messageIndex, address relayerRewardAddress) external;

    /**
     * @notice Retries the execution of a previously delivered message by verifying the payload matches
     * the hash of the payload originally delivered, and calling the destination address again.
     *
     * @dev Intended to be used if message excution failed on initial delivery of the Teleporter message.
     * For example, this may occur if the original required gas limit was not sufficient for the message
     * execution, or if the destination address did not contain a contract, but a compatible contract
     * was later deployed to that address. Messages are ensured to be successfully executed at most once.
     */
    function retryMessageExecution(bytes32 sourceBlockchainID, TeleporterMessage calldata message) external;

    /**
     * @notice Sends the receipts for the given `messageIDs`.
     *
     * @dev Sends the specified message receipts in a new message (with an empty payload) back to the source chain.
     * This is intended for use in sending receipts that have not been sent in a timely manner by the standard
     * receipt delivery mechanism.
     * @return The message ID of the newly sent message.
     */
    function sendSpecifiedReceipts(
        bytes32 sourceBlockchainID,
        bytes32[] calldata messageIDs,
        TeleporterFeeInfo calldata feeInfo,
        address[] calldata allowedRelayerAddresses
    ) external returns (bytes32);

    /**
     * @notice Sends any fee amount rewards for the given fee asset out to the caller.
     */
    function redeemRelayerRewards(address feeTokenAddress) external;

    /**
     * @notice Gets the hash of a given message stored in the EVM state, if the message exists.
     * @return The message hash
     */
    function getMessageHash(bytes32 messageID) external view returns (bytes32);

    /**
     * @notice Checks whether or not the given message has been received by this chain.
     * @return Boolean representing if the given message has been received.
     */
    function messageReceived(bytes32 messageID) external view returns (bool);

    /**
     * @notice Returns the address the relayer reward should be sent to on the source chain
     * for a given message, assuming that the message has already been delivered.
     * @return The relayer reward address for the given message.
     */
    function getRelayerRewardAddress(bytes32 messageID) external view returns (address);

    /**
     * @notice Gets the current reward amount of a given fee asset that is redeemable by the given relayer.
     * @return The amount of the fee asset redeemable by the specified relayer.
     */
    function checkRelayerRewardAmount(address relayer, address feeTokenAddress) external view returns (uint256);

    /**
     * @notice Gets the fee token address and amount for a given sent message.
     * @return The fee token address and fee amount for a the given sent message ID.
     * If the message ID is not found, zero address and amount values are returned.
     */
    function getFeeInfo(bytes32 messageID) external view returns (address, uint256);

    /**
     * @notice Gets the message ID that would currently be used for the next message sent from the contract
     * instance to the given destination blockchain.
     *
     * @dev This message ID may never be used in the event that the next call to sendCrossChainMessage in a
     * transaction uses a different destination blockchain. The current value as returned by this function will
     * change with each successful call to sendCrossChainMessage.
     * @return The specified message ID.
     */
    function getNextMessageID(bytes32 destinationBlockchainID) external view returns (bytes32);

    /**
     * @notice Gets the number of receipts that are waiting to be sent to the given source chain ID.
     * @return Size of the given queue.
     */
    function getReceiptQueueSize(bytes32 sourceBlockchainID) external view returns (uint256);

    /**
     * @notice Gets the receipt at the given index in the queue for the given source chain ID.
     * @return The receipt requested.
     */
    function getReceiptAtIndex(
        bytes32 sourceBlockchainID,
        uint256 index
    ) external view returns (TeleporterMessageReceipt memory);
}


// File contracts/Bridge/libs/Teleporter/ITeleporterReceiver.sol

// (c) 2022-2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: Ecosystem

pragma solidity 0.8.18;

/**
 * @dev Interface that cross-chain applications must implement to receive messages from Teleporter.
 *
 * @custom:security-contact https://github.com/ava-labs/teleporter/blob/main/SECURITY.md
 */
interface ITeleporterReceiver {
    /**
     * @dev Called by TeleporterMessenger on the receiving chain.
     *
     * @param sourceBlockchainID is provided by the TeleporterMessenger contract.
     * @param originSenderAddress is provided by the TeleporterMessenger contract.
     * @param message is the TeleporterMessage payload set by the sender.
     */
    function receiveTeleporterMessage(
        bytes32 sourceBlockchainID,
        address originSenderAddress,
        bytes calldata message
    ) external;
}


// File contracts/Bridge/libs/WarpMessenger/IWarpMessenger.sol

// (c) 2022-2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: MIT

pragma solidity ^0.8.0;

struct WarpMessage {
    bytes32 sourceChainID;
    address originSenderAddress;
    bytes payload;
}

struct WarpBlockHash {
    bytes32 sourceChainID;
    bytes32 blockHash;
}

interface IWarpMessenger {
    event SendWarpMessage(address indexed sender, bytes32 indexed messageID, bytes message);

    // sendWarpMessage emits a request for the subnet to send a warp message from [msg.sender]
    // with the specified parameters.
    // This emits a SendWarpMessage log from the precompile. When the corresponding block is accepted
    // the Accept hook of the Warp precompile is invoked with all accepted logs emitted by the Warp
    // precompile.
    // Each validator then adds the UnsignedWarpMessage encoded in the log to the set of messages
    // it is willing to sign for an off-chain relayer to aggregate Warp signatures.
    function sendWarpMessage(bytes calldata payload) external returns (bytes32 messageID);

    // getVerifiedWarpMessage parses the pre-verified warp message in the
    // predicate storage slots as a WarpMessage and returns it to the caller.
    // If the message exists and passes verification, returns the verified message
    // and true.
    // Otherwise, returns false and the empty value for the message.
    function getVerifiedWarpMessage(uint32 index) external view returns (WarpMessage calldata message, bool valid);

    // getVerifiedWarpBlockHash parses the pre-verified WarpBlockHash message in the
    // predicate storage slots as a WarpBlockHash message and returns it to the caller.
    // If the message exists and passes verification, returns the verified message
    // and true.
    // Otherwise, returns false and the empty value for the message.
    function getVerifiedWarpBlockHash(
        uint32 index
    ) external view returns (WarpBlockHash calldata warpBlockHash, bool valid);

    // getBlockchainID returns the snow.Context BlockchainID of this chain.
    // This blockchainID is the hash of the transaction that created this blockchain on the P-Chain
    // and is not related to the Ethereum ChainID.
    function getBlockchainID() external view returns (bytes32 blockchainID);
}


// File contracts/Bridge/libs/Teleporter/upgrades/TeleporterRegistry.sol

// (c) 2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: Ecosystem

pragma solidity 0.8.18;


// Registry entry that represents a mapping between protocolAddress and Teleporter version.
struct ProtocolRegistryEntry {
    uint256 version;
    address protocolAddress;
}

/**
 * @dev TeleporterRegistry contract provides an upgrade mechanism for {ITeleporterMessenger} contracts
 * through Warp off-chain messages
 *
 * @custom:security-contact https://github.com/ava-labs/teleporter/blob/main/SECURITY.md
 */
contract TeleporterRegistry {
    /**
     * @notice Address that the off-chain Warp message sets as the "source" address.
     * @dev The address is not owned by any EOA or smart contract account, so it
     * cannot possibly be the source address of any other Warp message emitted by the VM.
     */
    address public constant VALIDATORS_SOURCE_ADDRESS = address(0);

    /**
     * @notice Warp precompile used for sending and receiving Warp messages.
     */
    IWarpMessenger public constant WARP_MESSENGER = IWarpMessenger(0x0200000000000000000000000000000000000005);

    /**
     * @notice The blockchain ID of the chain the contract is deployed on.
     */
    bytes32 public immutable blockchainID;

    /**
     * @notice The maximum version increment allowed when adding a new protocol version.
     */
    uint256 public constant MAX_VERSION_INCREMENT = 500;

    /**
     * @notice The latest protocol version.
     * @dev 0 means no protocol version has been added, and isn't a valid version.
     */
    uint256 public latestVersion;

    /**
     * @notice Mappings that keep track of the protocol version and corresponding contract address.
     */
    mapping(uint256 version => address protocolAddress) private _versionToAddress;
    mapping(address protocolAddress => uint256 version) private _addressToVersion;

    /**
     * @notice Emitted when a new protocol version is added to the registry.
     */
    event AddProtocolVersion(uint256 indexed version, address indexed protocolAddress);

    /**
     * @notice Emitted when the latest version is updated.
     */
    event LatestVersionUpdated(uint256 indexed oldVersion, uint256 indexed newVersion);

    /**
     * @dev Initializes the contract by setting `blockchainID` and `latestVersion`.
     * Also adds the initial protocol versions to the registry.
     */
    constructor(ProtocolRegistryEntry[] memory initialEntries) {
        blockchainID = WARP_MESSENGER.getBlockchainID();

        uint256 length = initialEntries.length;
        for (uint256 i; i < length; ++i) {
            _addToRegistry(initialEntries[i]);
        }
    }

    /**
     * @dev Receives a Warp off-chain message containing a new protocol version and address to be registered,
     * and adds the new values to the respective mappings.
     * If a version is greater than the current latest version, it will be set as the latest version.
     * If a version is less than the current latest version, it is added to the registry, but
     * doesn't change the latest version.
     *
     * Emits a {AddProtocolVersion} event when successful.
     * Emits a {LatestVersionUpdated} event when a new protocol version greater than the current latest version is added.
     * Requirements:
     *
     * - a valid Warp off-chain message must be provided.
     * - source chain ID must be the same as the blockchain ID of the registry.
     * - origin sender address must be the same as the `VALIDATORS_SOURCE_ADDRESS`.
     * - destination address must be the same as the address of this registry.
     */
    function addProtocolVersion(uint32 messageIndex) external {
        // Get the verified Warp message, and check that it was sent to this registry via a Warp off-chain message.
        (WarpMessage memory message, bool success) = WARP_MESSENGER.getVerifiedWarpMessage(messageIndex);
        require(success, "TeleporterRegistry: invalid warp message");
        require(message.sourceChainID == blockchainID, "TeleporterRegistry: invalid source chain ID");
        // Check that the message is sent through a Warp off-chain message.
        require(
            message.originSenderAddress == VALIDATORS_SOURCE_ADDRESS,
            "TeleporterRegistry: invalid origin sender address"
        );

        (ProtocolRegistryEntry memory entry, address destinationAddress) = abi.decode(
            message.payload,
            (ProtocolRegistryEntry, address)
        );

        // Check that the message is sent to the registry.
        require(destinationAddress == address(this), "TeleporterRegistry: invalid destination address");

        _addToRegistry(entry);
    }

    /**
     * @dev Gets the latest {ITeleporterMessenger} contract.
     */
    function getLatestTeleporter() external view returns (ITeleporterMessenger) {
        return ITeleporterMessenger(getAddressFromVersion(latestVersion));
    }

    /**
     * @dev Gets the {ITeleporterMessenger} contract of the given `version`.
     * Requirements:
     *
     * - `version` must be a valid registered version.
     */
    function getTeleporterFromVersion(uint256 version) external view returns (ITeleporterMessenger) {
        return ITeleporterMessenger(getAddressFromVersion(version));
    }

    /**
     * @dev Gets the address of a protocol version.
     * Requirements:
     *
     * - `version` must be a valid registered version.
     */
    function getAddressFromVersion(uint256 version) public view returns (address) {
        require(version != 0, "TeleporterRegistry: zero version");
        address protocolAddress = _versionToAddress[version];
        require(protocolAddress != address(0), "TeleporterRegistry: version not found");
        return protocolAddress;
    }

    /**
     * @dev Gets the version of the given `protocolAddress`.
     * Requirements:
     *
     * - `protocolAddress` must be a valid registered protocol address.
     */
    function getVersionFromAddress(address protocolAddress) public view returns (uint256) {
        require(protocolAddress != address(0), "TeleporterRegistry: zero protocol address");
        uint256 version = _addressToVersion[protocolAddress];
        require(version != 0, "TeleporterRegistry: protocol address not found");
        return version;
    }

    /**
     * @dev Adds the new protocol version address to the registry.
     * Updates latest version if the version is greater than the current latest version.
     *
     * Emits a {AddProtocolVersion} event when successful.
     * Emits a {LatestVersionUpdated} event when a new protocol version greater than the current latest version is added.
     * Note: `entry.protocolAddress` doesn't have to be a contract address, allowing a new protocol address to be registered before the contract is deployed.
     * Requirements:
     *
     * - `entry.version` is not zero
     * - `entry.version` is not already registered
     * - `entry.protocolAddress` is not zero address
     */
    function _addToRegistry(ProtocolRegistryEntry memory entry) private {
        require(entry.version != 0, "TeleporterRegistry: zero version");
        // Check that the version has not previously been registered.
        require(_versionToAddress[entry.version] == address(0), "TeleporterRegistry: version already exists");
        require(entry.protocolAddress != address(0), "TeleporterRegistry: zero protocol address");

        uint256 latestVersion_ = latestVersion;
        require(
            entry.version <= latestVersion_ + MAX_VERSION_INCREMENT,
            "TeleporterRegistry: version increment too high"
        );

        _versionToAddress[entry.version] = entry.protocolAddress;

        // Since a protocol address can be registered multiple times,
        // only update the version if the new version is greater than the current version.
        if (entry.version > _addressToVersion[entry.protocolAddress]) {
            _addressToVersion[entry.protocolAddress] = entry.version;
        }
        emit AddProtocolVersion(entry.version, entry.protocolAddress);

        // Set latest version if the version is greater than the current latest version.
        if (entry.version > latestVersion_) {
            latestVersion = entry.version;
            emit LatestVersionUpdated(latestVersion_, entry.version);
        }
    }
}


// File contracts/Bridge/libs/Teleporter/upgrades/TeleporterUpgradeable.sol

// (c) 2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: Ecosystem

pragma solidity 0.8.18;







/**
 * @dev TeleporterUpgradeable provides upgrade utility for applications built on top
 * of the Teleporter protocol by integrating with the {TeleporterRegistry}.
 *
 * This contract is intended to be inherited by other contracts that wish to use the
 * upgrade mechanism. It provides an interface that restricts access to only Teleporter
 * versions that are greater than or equal to `minTeleporterVersion`.
 *
 * @custom:security-contact https://github.com/ava-labs/teleporter/blob/main/SECURITY.md
 */
abstract contract TeleporterUpgradeable is Context, ITeleporterReceiver, ReentrancyGuard {
    using SafeERC20 for IERC20;

    // The Teleporter registry contract manages different Teleporter contract versions.
    TeleporterRegistry public immutable teleporterRegistry;
    /**
     * @dev A mapping that keeps track of paused Teleporter addresses.
     */
    mapping(address teleporterAddress => bool paused) private _pausedTeleporterAddresses;

    /**
     * @dev The minimum required Teleporter version that the contract is allowed
     * to receive messages from. Should only be updated by `_setMinTeleporterVersion`
     */
    uint256 private _minTeleporterVersion;

    /**
     * @dev Emitted when `minTeleporterVersion` is updated.
     */
    event MinTeleporterVersionUpdated(uint256 indexed oldMinTeleporterVersion, uint256 indexed newMinTeleporterVersion);

    /**
     * @dev Emitted when a Teleporter address is paused.
     */
    event TeleporterAddressPaused(address indexed teleporterAddress);

    /**
     * @dev Emitted when a Teleporter address is unpaused.
     */
    event TeleporterAddressUnpaused(address indexed teleporterAddress);

    /**
     * @dev Initializes the {TeleporterUpgradeable} contract by getting `teleporterRegistry`
     * instance and setting `_minTeleporterVersion`.
     */
    constructor(address teleporterRegistryAddress) {
        require(teleporterRegistryAddress != address(0), "TeleporterUpgradeable: zero teleporter registry address");

        teleporterRegistry = TeleporterRegistry(teleporterRegistryAddress);
        _minTeleporterVersion = teleporterRegistry.latestVersion();
    }

    /**
     * @dev See {ITeleporterReceiver-receiveTeleporterMessage}
     * `nonReentrant` is a reentrancy guard that protects again multiple versions of the
     * TeleporterMessengerContract delivering a message in the same call. Any internal calls
     * will not be able to call functions also marked with `nonReentrant`.
     *
     * Requirements:
     *
     * - `_msgSender()` must be a Teleporter version greater than or equal to `minTeleporterVersion`.
     */
    function receiveTeleporterMessage(
        bytes32 sourceBlockchainID,
        address originSenderAddress,
        bytes calldata message
    ) external nonReentrant {
        // Checks that `_msgSender()` matches a Teleporter version greater than or equal to `minTeleporterVersion`.
        require(
            teleporterRegistry.getVersionFromAddress(_msgSender()) >= _minTeleporterVersion,
            "TeleporterUpgradeable: invalid Teleporter sender"
        );

        // Check against the paused Teleporter addresses.
        require(!isTeleporterAddressPaused(_msgSender()), "TeleporterUpgradeable: Teleporter address paused");

        _receiveTeleporterMessage(sourceBlockchainID, originSenderAddress, message);
    }

    /**
     * @dev Updates the minimum Teleporter version allowed for delivering Teleporer messages
     * to this contract.
     *
     * To prevent anyone from being able to call this function, which would disallow messages
     * from old Teleporter versions from being received, this function should be safeguarded with access
     * controls. This is done by overriding the implementation of {_checkTeleporterUpgradeAccess}.
     */
    function updateMinTeleporterVersion(uint256 version) public virtual {
        _checkTeleporterUpgradeAccess();
        _setMinTeleporterVersion(version);
    }

    /**
     * @dev Pauses a Teleporter address from interacting with this contract.
     * After pausing a Teleporter address, it will no longer be able to deliver messages
     * to this contract, and this contract will not send messages through that Teleporter address.
     * The address does not need to be registered with the Teleporter registry.
     * Emits a {TeleporterAddressPaused} event if successfully paused.
     * Requirements:
     *
     * - `_msgSender()` must have Teleporter upgrade access.
     * - `teleporterAddress` is not the zero address.
     * - `teleporterAddress` is not already paused.
     */
    function pauseTeleporterAddress(address teleporterAddress) public virtual {
        _checkTeleporterUpgradeAccess();
        require(teleporterAddress != address(0), "TeleporterUpgradeable: zero Teleporter address");
        require(!isTeleporterAddressPaused(teleporterAddress), "TeleporterUpgradeable: address already paused");
        _pausedTeleporterAddresses[teleporterAddress] = true;
        emit TeleporterAddressPaused(teleporterAddress);
    }

    /**
     * @dev Unpauses a Teleporter address from interacting with this contract.
     * After unpausing a Teleporter address, it will again be able to deliver messages
     * to this contract, and this contract can send messages through that Teleporter address.
     * The address does not need to be registered with the Teleporter registry.
     * Emits a {TeleporterAddressUnpaused} event if successfully unpaused.
     * Requirements:
     *
     * - `_msgSender()` must have Teleporter upgrade access.
     * - `teleporterAddress` is not the zero address.
     * - `teleporterAddress` is already paused.
     */
    function unpauseTeleporterAddress(address teleporterAddress) public virtual {
        _checkTeleporterUpgradeAccess();
        require(teleporterAddress != address(0), "TeleporterUpgradeable: zero Teleporter address");
        require(isTeleporterAddressPaused(teleporterAddress), "TeleporterUpgradeable: address not paused");
        emit TeleporterAddressUnpaused(teleporterAddress);
        _pausedTeleporterAddresses[teleporterAddress] = false;
    }

    /**
     * @dev Public getter for `_minTeleporterVersion`.
     */
    function getMinTeleporterVersion() public view returns (uint256) {
        return _minTeleporterVersion;
    }

    /**
     * @dev Checks if a Teleporter address is paused.
     */
    function isTeleporterAddressPaused(address teleporterAddress) public view virtual returns (bool) {
        return _pausedTeleporterAddresses[teleporterAddress];
    }

    /**
     * @dev Sets the minimum Teleporter version allowed for delivering Teleporter messages.
     * Emits a {MinTeleporterVersionUpdated} event if the minimum Teleporter version was updated.
     * Requirements:
     *
     * - `version` must be less than or equal to the latest Teleporter version.
     * - `version` must be greater than the current minimum Teleporter version.
     *
     */
    function _setMinTeleporterVersion(uint256 version) internal virtual {
        uint256 latestTeleporterVersion = teleporterRegistry.latestVersion();
        uint256 oldMinTeleporterVersion = _minTeleporterVersion;

        require(version <= latestTeleporterVersion, "TeleporterUpgradeable: invalid Teleporter version");
        require(version > oldMinTeleporterVersion, "TeleporterUpgradeable: not greater than current minimum version");

        _minTeleporterVersion = version;
        emit MinTeleporterVersionUpdated(oldMinTeleporterVersion, version);
    }

    /**
     * @dev Receives Teleporter messages and handles accordingly.
     * This function should be overridden by contracts that inherit from this contract.
     */
    function _receiveTeleporterMessage(
        bytes32 sourceBlockchainID,
        address originSenderAddress,
        bytes memory message
    ) internal virtual;

    /**
     * @dev Checks that the caller has access to update the minimum Teleporter version
     * allowed for delivering Teleporter messages to this contract.
     *
     * This function should be overridden by contracts that inherit from this contract.
     */
    function _checkTeleporterUpgradeAccess() internal virtual;

    /**
     * @dev Sends a cross chain message using the TeleporterMessenger contract.
     *
     * The fee amount should be transferred to this contract prior to calling this function.
     * The fee amount is then allocated from this contract's token balance to
     * Teleporter's allowance to pay for sending the message.
     *
     * @return `messageID` The unique identifier for the Teleporter message.
     */
    function _sendTeleporterMessage(TeleporterMessageInput memory messageInput) internal virtual returns (bytes32) {
        ITeleporterMessenger teleporterMessenger = _getTeleporterMessenger();
        // For non-zero fee amounts increase the Teleporter contract's allowance.
        if (messageInput.feeInfo.amount > 0) {
            require(
                messageInput.feeInfo.feeTokenAddress != address(0),
                "TeleporterUpgradeable: zero fee token address"
            );
            IERC20(messageInput.feeInfo.feeTokenAddress).safeIncreaseAllowance(
                address(teleporterMessenger),
                messageInput.feeInfo.amount
            );
        }
        return teleporterMessenger.sendCrossChainMessage(messageInput);
    }

    /**
     * @dev Returns the Teleporter messenger used to send Teleporter messages,
     * and checks that the Teleporter messenger is not paused.
     *
     * By default returns the latest Teleporter messenger, but can be overriden to
     * return a Teleporter messenger of a specific version.
     */
    function _getTeleporterMessenger() internal view virtual returns (ITeleporterMessenger) {
        ITeleporterMessenger teleporter = teleporterRegistry.getLatestTeleporter();
        require(!isTeleporterAddressPaused(address(teleporter)), "TeleporterUpgradeable: Teleporter sending paused");

        return teleporter;
    }
}


// File contracts/Bridge/libs/Teleporter/upgrades/TeleporterOwnerUpgradeable.sol

// (c) 2023, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Original license: SPDX_License_Identifier: Ecosystem

pragma solidity 0.8.18;


/**
 * @dev Contract that inherits {TeleporterUpgradeable} and allows
 * only owners of the contract to update the minimum Teleporter version.
 *
 * @custom:security-contact https://github.com/ava-labs/teleporter/blob/main/SECURITY.md
 */
abstract contract TeleporterOwnerUpgradeable is TeleporterUpgradeable, Ownable {
    constructor(
        address teleporterRegistryAddress,
        address initialOwner
    ) TeleporterUpgradeable(teleporterRegistryAddress) {
        transferOwnership(initialOwner);
    }

    /**
     * @dev See {TeleporterUpgradeable-_checkTeleporterUpgradeAccess}
     *
     * Checks that the caller is the owner of the contract for upgrade access.
     */
    function _checkTeleporterUpgradeAccess() internal view virtual override {
        _checkOwner();
    }
}


// File contracts/Bridge/SourceChain/ISourceBridge.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.18;

interface ISourceBridge {
    enum BridgeAction {
        TokenCreate,
        ERC721Create,
        ERC1155Create,
        MintTokens,
        MintERC721,
        MintERC1155,
        UnlockTokens,
        UnlockERC721,
        UnlockERC1155
    }
    struct RequestBridgeTokenInfo {
        bytes32 destinationBlockchainID;
        address destinationBridgeAddress;
        address sourceTokenAddress;
        address sender;
        address recipient;
        uint256 amount;
    }
    struct RequestBridgeERC721Info {
        bytes32 destinationBlockchainID;
        address destinationBridgeAddress;
        address sourceTokenAddress;
        address sender;
        address recipient;
        uint256[] tokenIds;
    }
    struct RequestBridgeERC1155Info {
        bytes32 destinationBlockchainID;
        address destinationBridgeAddress;
        address sourceTokenAddress;
        address sender;
        address recipient;
        uint256[] tokenIds;
        uint256[] amounts;
    }
    struct SourceTokenInfo {
        address sourceTokenAddress;
        uint8 tokenType;
        string defaultBaseURI;
    }
    event BridgeTokens(
        address indexed sourceTokenAddress,
        bytes32 indexed destinationBlockchainID,
        bytes32 indexed teleporterMessageID,
        address destinationBridgeAddress,
        address sender,
        address recipient,
        uint256 amount
    );
    event BridgeERC721(
        address indexed sourceTokenAddress,
        bytes32 indexed destinationBlockchainID,
        bytes32 indexed teleporterMessageID,
        address destinationBridgeAddress,
        address sender,
        address recipient,
        uint256[] tokenIds
    );
    event BridgeERC1155(
        address indexed sourceTokenAddress,
        bytes32 indexed destinationBlockchainID,
        bytes32 indexed teleporterMessageID,
        address destinationBridgeAddress,
        address sender,
        address recipient,
        uint256[] tokenIds,
        uint256[] amounts
    );
    event SubmitCreateBridgeToken(
        bytes32 indexed destinationBlockchainID,
        address indexed destinationBridgeAddress,
        address indexed sourceTokenAddress,
        uint8 tokenType,
        bytes32 teleporterMessageID
    );
    event ClearedAllowedRelayer();
    event TellerChanged(address previousTeller, address indexed newTeller);
    event NewRelayerAdded(address indexed newRelayerAddress);

    /* solhint-enable */

    function bridgeTokens(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address destinationTokenAddress,
        address sender,
        address recipient,
        uint256 amount
    ) external payable;

    function bridgeERC721(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address sender,
        address recipient,
        uint256[] memory tokenIds
    ) external;

    function bridgeERC1155(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address sender,
        address recipient,
        uint256[] memory tokenIds,
        uint256[] memory amounts
    ) external;
}


// File contracts/Bridge/SourceChain/SourceBridge.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.18;













contract SourceBridge is
    ERC2771Context,
    ISourceBridge,
    TeleporterOwnerUpgradeable,
    ERC721Holder,
    ERC1155Holder,
    NextOwnablePausable
{
    using SafeERC20 for ERC20;

    address public constant NATIVE_TOKEN = 0x0200000000000000000000000000000000000001;
    address public constant WARP_PRECOMPILE_ADDRESS = 0x0200000000000000000000000000000000000005;
    uint256 public constant CREATE_BRIDGE_TOKENS_REQUIRED_GAS = 3_000_000;
    uint256 public constant MINT_BRIDGE_TOKENS_REQUIRED_GAS = 200_000;
    bytes32 public immutable currentBlockchainID;

    address private _teller;
    address[] private _allowedRelayers;

    mapping(bytes32 destinationBlockchainID => mapping(address destinationBridgeAddress => mapping(address originTokenAddress => uint8 createdTokenType)))
        public submittedBridgeTokenCreations;
    mapping(bytes32 destinationBlockchainID => mapping(address destinationBridgeAddress => mapping(address originTokenAddress => uint256 balance)))
        public bridgedBalances;
    mapping(bytes32 destinationBlockchainID => mapping(address destinationBridgeAddress => mapping(address originTokenAddress => mapping(uint256 tokenId => bool bridged))))
        public bridgedNft;
    mapping(bytes32 destinationBlockchainID => mapping(address destinationBridgeAddress => mapping(address originTokenAddress => mapping(uint256 tokenId => uint256 amount))))
        public bridgedFts;

    modifier validAddress(address addr) {
        require(addr != address(0), "SourceBridge/invalidAddress: couldn't be zero address");
        _;
    }

    constructor(
        address trustedForwarder,
        address teleporterRegistryAddress,
        address teleporterManager
    )
        ERC2771Context(trustedForwarder)
        TeleporterOwnerUpgradeable(teleporterRegistryAddress, teleporterManager)
        validAddress(trustedForwarder)
        validAddress(teleporterRegistryAddress)
        validAddress(teleporterManager)
    {
        currentBlockchainID = IWarpMessenger(WARP_PRECOMPILE_ADDRESS).getBlockchainID();
    }

    /**
     * @notice Bridges Native tokens or ERC20 tokens to a destination blockchain.
     * @dev If the token address is the same as the native token minter address, it works as a native token bridge function.
     * @param destinationBlockchainID The ID of the destination blockchain.
     * @param destinationBridgeAddress The address of the bridge on the destination blockchain.
     * @param sourceTokenAddress The address of the token on the source blockchain.
     * @param sender The sender address on the source blockchain.
     * @param recipient The recipient address on the destination blockchain.
     * @param amount The amount of tokens to bridge.
     */
    function bridgeTokens(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address sender,
        address recipient,
        uint256 amount
    )
        external
        payable
        nonReentrant
        whenNotPaused
        validAddress(destinationBridgeAddress)
        validAddress(sourceTokenAddress)
        validAddress(recipient)
    {
        if (_msgSender() != _teller) {
            require(_msgSender() == sender, "SourceBridge/invalidRequest: cannot bridge others' assets");
        }

        require(
            destinationBlockchainID != currentBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        if (sourceTokenAddress == NATIVE_TOKEN) {
            require(
                submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][sourceTokenAddress] ==
                    1,
                "SourceBridge/invalidRequest: invalid bridge token address"
            );
            require(msg.value == amount, "SourceBridge/wrongAmount: wrong value or amount");
        } else {
            require(
                submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][sourceTokenAddress] ==
                    2,
                "SourceBridge/invalidRequest: invalid bridge token address"
            );
            require(msg.value == 0, "SourceBridge/wrongValue: value must be 0");
        }

        return
            _processWrappedTokenMint(
                RequestBridgeTokenInfo({
                    destinationBlockchainID: destinationBlockchainID,
                    destinationBridgeAddress: destinationBridgeAddress,
                    sourceTokenAddress: sourceTokenAddress,
                    sender: sender,
                    recipient: recipient,
                    amount: amount
                })
            );
    }

    /**
     * @notice Bridges ERC721 tokens to a destination blockchain.
     * @param destinationBlockchainID The ID of the destination blockchain.
     * @param destinationBridgeAddress The address of the bridge on the destination blockchain.
     * @param sourceTokenAddress The address of the ERC721 token on the source blockchain.
     * @param sender The sender address on the source blockchain.
     * @param recipient The recipient address on the destination blockchain.
     * @param tokenIds The IDs of the ERC721 tokens to bridge.
     */
    function bridgeERC721(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address sender,
        address recipient,
        uint256[] memory tokenIds
    )
        external
        nonReentrant
        whenNotPaused
        validAddress(destinationBridgeAddress)
        validAddress(sourceTokenAddress)
        validAddress(recipient)
    {
        if (_msgSender() != _teller) {
            require(_msgSender() == sender, "SourceBridge/invalidRequest: cannot bridge others' assets");
        }

        require(
            destinationBlockchainID != currentBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        require(
            submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][sourceTokenAddress] == 3,
            "SourceBridge/invalidRequest: invalid bridge token address"
        );

        return
            _processERC721Mint(
                RequestBridgeERC721Info({
                    destinationBlockchainID: destinationBlockchainID,
                    destinationBridgeAddress: destinationBridgeAddress,
                    sourceTokenAddress: sourceTokenAddress,
                    sender: sender,
                    recipient: recipient,
                    tokenIds: tokenIds
                })
            );
    }

    /**
     * @notice Bridges ERC1155 tokens to a destination blockchain.
     * @param destinationBlockchainID The ID of the destination blockchain.
     * @param destinationBridgeAddress The address of the bridge on the destination blockchain.
     * @param sourceTokenAddress The address of the ERC1155 token on the source blockchain.
     * @param sender The sender address on the source blockchain.
     * @param recipient The recipient address on the destination blockchain.
     * @param tokenIds The IDs of the ERC1155 tokens to bridge.
     * @param amounts The amounts of each ERC1155 token to bridge.
     */
    function bridgeERC1155(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address sender,
        address recipient,
        uint256[] memory tokenIds,
        uint256[] memory amounts
    )
        external
        nonReentrant
        whenNotPaused
        validAddress(destinationBridgeAddress)
        validAddress(sourceTokenAddress)
        validAddress(recipient)
    {
        if (_msgSender() != _teller) {
            require(_msgSender() == sender, "SourceBridge/invalidRequest: cannot bridge others' assets");
        }

        require(
            destinationBlockchainID != currentBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        require(
            submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][sourceTokenAddress] == 4,
            "SourceBridge/invalidRequest: invalid bridge token address"
        );

        return
            _processERC1155Mint(
                RequestBridgeERC1155Info({
                    destinationBlockchainID: destinationBlockchainID,
                    destinationBridgeAddress: destinationBridgeAddress,
                    sourceTokenAddress: sourceTokenAddress,
                    sender: sender,
                    recipient: recipient,
                    tokenIds: tokenIds,
                    amounts: amounts
                })
            );
    }

    /**
     * @notice Submits a request to create a bridge token on a destination blockchain.
     * @dev The function validates the destination bridge address, ensures that a bridge token creation request does not already exist for the given parameters,
     * and then encodes and sends the appropriate message data for creating the bridge token.
     * @dev Token type 1. Native token / 2. ERC20 / 3. ERC721 / 4. ERC1155
     * @param destinationBlockchainID The ID of the destination blockchain.
     * @param destinationBridgeAddress The address of the bridge on the destination blockchain.
     * @param sourceTokenInfo Information about the source token including its address, type, and other relevant details.
     */
    function submitCreateBridgeToken(
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        SourceTokenInfo memory sourceTokenInfo
    )
        external
        nonReentrant
        whenExecutable
        validAddress(destinationBridgeAddress)
        validAddress(sourceTokenInfo.sourceTokenAddress)
    {
        require(
            submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][
                sourceTokenInfo.sourceTokenAddress
            ] == 0,
            "SourceBridge/invalidRequest: contract already exist"
        );
        bytes memory messageData;

        if (sourceTokenInfo.tokenType == 1) {
            messageData = _encodeCreateBridgeTokenData(
                sourceTokenInfo.sourceTokenAddress,
                // nativeToken name and symbol
                "NXPC",
                "NXPC",
                18
            );
        } else if (sourceTokenInfo.tokenType == 2) {
            ERC20 sourceToken = ERC20(sourceTokenInfo.sourceTokenAddress);
            messageData = _encodeCreateBridgeTokenData(
                sourceTokenInfo.sourceTokenAddress,
                sourceToken.name(),
                sourceToken.symbol(),
                sourceToken.decimals()
            );
        } else if (sourceTokenInfo.tokenType == 3) {
            ERC721 sourceToken = ERC721(sourceTokenInfo.sourceTokenAddress);
            messageData = _encodeCreateBridgeERC721Data(
                sourceTokenInfo.sourceTokenAddress,
                sourceToken.name(),
                sourceToken.symbol(),
                sourceTokenInfo.defaultBaseURI
            );
        } else if (sourceTokenInfo.tokenType == 4) {
            messageData = _encodeCreateBridgeERC1155Data(
                sourceTokenInfo.sourceTokenAddress,
                sourceTokenInfo.defaultBaseURI
            );
        } else {
            revert("SourceBridge/invalidRequest: invalid token type");
        }

        submittedBridgeTokenCreations[destinationBlockchainID][destinationBridgeAddress][
            sourceTokenInfo.sourceTokenAddress
        ] = sourceTokenInfo.tokenType;

        ITeleporterMessenger teleporterMessenger = _getTeleporterMessenger();
        bytes32 messageID = teleporterMessenger.sendCrossChainMessage(
            TeleporterMessageInput({
                destinationBlockchainID: destinationBlockchainID,
                destinationAddress: destinationBridgeAddress,
                feeInfo: TeleporterFeeInfo({ feeTokenAddress: address(0), amount: 0 }),
                requiredGasLimit: CREATE_BRIDGE_TOKENS_REQUIRED_GAS,
                allowedRelayerAddresses: _allowedRelayers,
                message: messageData
            })
        );
        emit SubmitCreateBridgeToken(
            destinationBlockchainID,
            destinationBridgeAddress,
            sourceTokenInfo.sourceTokenAddress,
            sourceTokenInfo.tokenType,
            messageID
        );
    }

    /**
     * @notice Sets a new teller contract address.
     * @dev A teller is an address that temporarily stores the bridge-requested assets of the user listed on the blocklist.
     * @param newTeller The new teller address.
     */
    function setTeller(address newTeller) external onlyOwner {
        emit TellerChanged(_teller, newTeller);
        _teller = newTeller;
    }

    /**
     * @notice Adds a new relayer address to the allowed relayers list.
     * @param newRelayerAddress The address of the new relayer to be added.
     */
    function addAllowedRelayer(address newRelayerAddress) external onlyOwner validAddress(newRelayerAddress) {
        emit NewRelayerAdded(newRelayerAddress);
        _allowedRelayers.push(newRelayerAddress);
    }

    /**
     * @notice Clears all addresses from the allowed relayers list.
     */
    function clearAllowedRelayer() external onlyOwner {
        emit ClearedAllowedRelayer();
        _allowedRelayers = new address[](0);
    }

    /**
     * @notice Gets the current teller address.
     * @return address The address of the current teller.
     */
    function getTeller() external view returns (address) {
        return _teller;
    }

    /**
     * @notice Gets the list of allowed relayer addresses.
     * @return address[] An array of addresses that are allowed as relayers.
     */
    function getAllowedRelayerAddresses() external view returns (address[] memory) {
        return _allowedRelayers;
    }

    function _receiveTeleporterMessage(
        bytes32 sourceBlockchainID,
        address originSenderAddress,
        bytes memory message
    ) internal override {
        (BridgeAction action, bytes memory actionData) = abi.decode(message, (BridgeAction, bytes));

        if (action == BridgeAction.UnlockTokens) {
            (
                bytes32 destinationBlockchainID,
                address destinationBridgeAddress,
                address sourceTokenAddress,
                address recipient,
                uint256 amount
            ) = abi.decode(actionData, (bytes32, address, address, address, uint256));
            _unlockBridgeToken({
                sourceBlockchainID: sourceBlockchainID,
                sourceBridgeAddress: originSenderAddress,
                destinationBlockchainID: destinationBlockchainID,
                destinationBridgeAddress: destinationBridgeAddress,
                sourceTokenAddress: sourceTokenAddress,
                recipient: recipient,
                amount: amount
            });
        } else if (action == BridgeAction.UnlockERC721) {
            (
                bytes32 destinationBlockchainID,
                address destinationBridgeAddress,
                address sourceTokenAddress,
                address recipient,
                uint256[] memory tokenIds
            ) = abi.decode(actionData, (bytes32, address, address, address, uint256[]));
            _unlockBridgeERC721({
                sourceBlockchainID: sourceBlockchainID,
                sourceBridgeAddress: originSenderAddress,
                destinationBlockchainID: destinationBlockchainID,
                destinationBridgeAddress: destinationBridgeAddress,
                sourceTokenAddress: sourceTokenAddress,
                recipient: recipient,
                tokenIds: tokenIds
            });
        } else if (action == BridgeAction.UnlockERC1155) {
            (
                bytes32 destinationBlockchainID,
                address destinationBridgeAddress,
                address sourceTokenAddress,
                address recipient,
                uint256[] memory tokenIds,
                uint256[] memory amounts
            ) = abi.decode(actionData, (bytes32, address, address, address, uint256[], uint256[]));
            _unlockBridgeERC1155({
                sourceBlockchainID: sourceBlockchainID,
                sourceBridgeAddress: originSenderAddress,
                destinationBlockchainID: destinationBlockchainID,
                destinationBridgeAddress: destinationBridgeAddress,
                sourceTokenAddress: sourceTokenAddress,
                recipient: recipient,
                tokenIds: tokenIds,
                amounts: amounts
            });
        } else {
            revert("SourceBridge/invalidRequest: invalid action data");
        }
    }

    /**
     * @notice Encodes the data required to create a bridge token.
     * @dev The encoded data includes the origin contract address, token name, token symbol, and token decimals.
     * @param originContractAddress The address of the original token contract.
     * @param tokenName The name of the token.
     * @param tokenSymbol The symbol of the token.
     * @param tokenDecimals The number of decimals of the token.
     * @return bytes The encoded data as bytes.
     */
    function _encodeCreateBridgeTokenData(
        address originContractAddress,
        string memory tokenName,
        string memory tokenSymbol,
        uint8 tokenDecimals
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, tokenName, tokenSymbol, tokenDecimals);
        return abi.encode(BridgeAction.TokenCreate, paramsData);
    }

    /**
     * @notice Encodes the data required to create a bridge ERC721 token.
     * @dev The encoded data includes the origin contract address, token name, token symbol, and base URI.
     * @param originContractAddress The address of the original ERC721 token contract.
     * @param tokenName The name of the ERC721 token.
     * @param tokenSymbol The symbol of the ERC721 token.
     * @param uri_ The base URI of the ERC721 token.
     * @return bytes The encoded data as bytes.
     */
    function _encodeCreateBridgeERC721Data(
        address originContractAddress,
        string memory tokenName,
        string memory tokenSymbol,
        string memory uri_
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, tokenName, tokenSymbol, uri_);
        return abi.encode(BridgeAction.ERC721Create, paramsData);
    }

    /**
     * @notice Encodes the data required to create a bridge ERC1155 token.
     * @dev The encoded data includes the origin contract address and base URI.
     * @param originContractAddress The address of the original ERC1155 token contract.
     * @param uri_ The base URI of the ERC1155 token.
     * @return bytes The encoded data as bytes.
     */
    function _encodeCreateBridgeERC1155Data(
        address originContractAddress,
        string memory uri_
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, uri_);
        return abi.encode(BridgeAction.ERC1155Create, paramsData);
    }

    /**
     * @notice Encodes the data required to mint wrapped tokens.
     * @dev The encoded data includes the origin contract address, recipient address, and amount to be bridged.
     * @param originContractAddress The address of the original token contract.
     * @param recipient The address of the recipient.
     * @param bridgeAmount The amount of tokens to be bridged.
     * @return bytes The encoded data as bytes.
     */
    function _encodeMintWrappedTokenData(
        address originContractAddress,
        address recipient,
        uint256 bridgeAmount
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, recipient, bridgeAmount);
        return abi.encode(BridgeAction.MintTokens, paramsData);
    }

    /**
     * @notice Encodes the data required to mint ERC721 tokens.
     * @dev The encoded data includes the origin contract address, recipient address, and token IDs to be bridged.
     * @param originContractAddress The address of the original ERC721 token contract.
     * @param recipient The address of the recipient.
     * @param tokenIds The IDs of the tokens to be bridged.
     * @return bytes The encoded data as bytes.
     */
    function _encodeMintERC721Data(
        address originContractAddress,
        address recipient,
        uint256[] memory tokenIds
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, recipient, tokenIds);
        return abi.encode(BridgeAction.MintERC721, paramsData);
    }

    /**
     * @notice Encodes the data required to mint ERC1155 tokens.
     * @dev The encoded data includes the origin contract address, recipient address, token IDs, and amounts to be bridged.
     * @param originContractAddress The address of the original ERC1155 token contract.
     * @param recipient The address of the recipient.
     * @param tokenIds The IDs of the tokens to be bridged.
     * @param bridgeAmounts The amounts of tokens to be bridged.
     * @return bytes The encoded data as bytes.
     */
    function _encodeMintERC1155Data(
        address originContractAddress,
        address recipient,
        uint256[] memory tokenIds,
        uint256[] memory bridgeAmounts
    ) internal pure returns (bytes memory) {
        bytes memory paramsData = abi.encode(originContractAddress, recipient, tokenIds, bridgeAmounts);
        return abi.encode(BridgeAction.MintERC1155, paramsData);
    }

    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }

    function _unlockBridgeToken(
        bytes32 sourceBlockchainID,
        address sourceBridgeAddress,
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address recipient,
        uint256 amount
    ) private {
        require(
            sourceBlockchainID != destinationBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        require(
            destinationBridgeAddress == address(this),
            "SourceBridge/invalidRequest: invalid destination bridge address"
        );

        uint256 currentBalance = bridgedBalances[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress];
        require(currentBalance >= amount, "SourceBridge/wrongAmount: insufficient balance");

        if (sourceTokenAddress == NATIVE_TOKEN) {
            unchecked {
                bridgedBalances[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress] = currentBalance - amount;
            }
            (bool success, ) = recipient.call{ value: amount }("");
            require(success, "SourceBridge/transferFailed: Transfer failed");
            return;
        }
        unchecked {
            bridgedBalances[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress] = currentBalance - amount;
        }
        ERC20(sourceTokenAddress).safeTransfer(recipient, amount);
        return;
    }

    function _unlockBridgeERC721(
        bytes32 sourceBlockchainID,
        address sourceBridgeAddress,
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address recipient,
        uint256[] memory tokenIds
    ) private {
        require(
            sourceBlockchainID != destinationBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        require(
            destinationBridgeAddress == address(this),
            "SourceBridge/invalidRequest: invalid destination bridge address"
        );

        uint256 tokenLength = tokenIds.length;

        for (uint256 i; i < tokenLength; ) {
            bool isBridgedNft = bridgedNft[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress][tokenIds[i]];
            require(isBridgedNft, "SourceBridge/wrongAmount: insufficient balance");

            bridgedNft[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress][tokenIds[i]] = false;
            ERC721(sourceTokenAddress).safeTransferFrom(address(this), recipient, tokenIds[i]);
            unchecked {
                i++;
            }
        }

        return;
    }

    function _unlockBridgeERC1155(
        bytes32 sourceBlockchainID,
        address sourceBridgeAddress,
        bytes32 destinationBlockchainID,
        address destinationBridgeAddress,
        address sourceTokenAddress,
        address recipient,
        uint256[] memory tokenIds,
        uint256[] memory amounts
    ) private {
        require(
            sourceBlockchainID != destinationBlockchainID,
            "SourceBridge/invalidRequest: cannot bridge to same chain"
        );
        require(
            destinationBridgeAddress == address(this),
            "SourceBridge/invalidRequest: invalid destination bridge address"
        );

        uint256 tokenLength = tokenIds.length;
        for (uint256 i; i < tokenLength; ) {
            uint256 currentBalance = bridgedFts[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress][
                tokenIds[i]
            ];
            require(currentBalance >= amounts[i], "SourceBridge/wrongAmount: insufficient balance");

            unchecked {
                bridgedFts[sourceBlockchainID][sourceBridgeAddress][sourceTokenAddress][tokenIds[i]] =
                    currentBalance -
                    amounts[i];
            }
            ERC1155(sourceTokenAddress).safeTransferFrom(address(this), recipient, tokenIds[i], amounts[i], "");
            unchecked {
                i++;
            }
        }
        return;
    }

    function _processWrappedTokenMint(RequestBridgeTokenInfo memory requestBridgeTokenInfo) private {
        if (requestBridgeTokenInfo.sourceTokenAddress != NATIVE_TOKEN) {
            ERC20(requestBridgeTokenInfo.sourceTokenAddress).transferFrom(
                requestBridgeTokenInfo.sender,
                address(this),
                requestBridgeTokenInfo.amount
            );
        }

        bridgedBalances[requestBridgeTokenInfo.destinationBlockchainID][
            requestBridgeTokenInfo.destinationBridgeAddress
        ][requestBridgeTokenInfo.sourceTokenAddress] += requestBridgeTokenInfo.amount;

        bytes memory messageData = _encodeMintWrappedTokenData({
            originContractAddress: requestBridgeTokenInfo.sourceTokenAddress,
            recipient: requestBridgeTokenInfo.recipient,
            bridgeAmount: requestBridgeTokenInfo.amount
        });

        ITeleporterMessenger teleporterMessenger = _getTeleporterMessenger();
        bytes32 messageID = teleporterMessenger.sendCrossChainMessage(
            TeleporterMessageInput({
                destinationBlockchainID: requestBridgeTokenInfo.destinationBlockchainID,
                destinationAddress: requestBridgeTokenInfo.destinationBridgeAddress,
                feeInfo: TeleporterFeeInfo({ feeTokenAddress: address(0), amount: 0 }),
                requiredGasLimit: MINT_BRIDGE_TOKENS_REQUIRED_GAS,
                allowedRelayerAddresses: _allowedRelayers,
                message: messageData
            })
        );

        emit BridgeTokens({
            sourceTokenAddress: requestBridgeTokenInfo.sourceTokenAddress,
            destinationBlockchainID: requestBridgeTokenInfo.destinationBlockchainID,
            teleporterMessageID: messageID,
            destinationBridgeAddress: requestBridgeTokenInfo.destinationBridgeAddress,
            sender: requestBridgeTokenInfo.sender,
            recipient: requestBridgeTokenInfo.recipient,
            amount: requestBridgeTokenInfo.amount
        });
    }

    function _processERC721Mint(RequestBridgeERC721Info memory requestBridgeERC721Info) private {
        uint256 tokenLength = requestBridgeERC721Info.tokenIds.length;
        uint256 requiredGas = tokenLength * MINT_BRIDGE_TOKENS_REQUIRED_GAS;
        require(requiredGas < 15000000, "SourceBridge/overBlockGas: too much tokens");

        for (uint256 i; i < tokenLength; ) {
            ERC721(requestBridgeERC721Info.sourceTokenAddress).safeTransferFrom(
                requestBridgeERC721Info.sender,
                address(this),
                requestBridgeERC721Info.tokenIds[i]
            );

            bridgedNft[requestBridgeERC721Info.destinationBlockchainID][
                requestBridgeERC721Info.destinationBridgeAddress
            ][requestBridgeERC721Info.sourceTokenAddress][requestBridgeERC721Info.tokenIds[i]] = true;

            unchecked {
                i++;
            }
        }
        bytes memory messageData = _encodeMintERC721Data({
            originContractAddress: requestBridgeERC721Info.sourceTokenAddress,
            recipient: requestBridgeERC721Info.recipient,
            tokenIds: requestBridgeERC721Info.tokenIds
        });

        ITeleporterMessenger teleporterMessenger = _getTeleporterMessenger();
        bytes32 messageID = teleporterMessenger.sendCrossChainMessage(
            TeleporterMessageInput({
                destinationBlockchainID: requestBridgeERC721Info.destinationBlockchainID,
                destinationAddress: requestBridgeERC721Info.destinationBridgeAddress,
                feeInfo: TeleporterFeeInfo({ feeTokenAddress: address(0), amount: 0 }),
                requiredGasLimit: requiredGas,
                allowedRelayerAddresses: _allowedRelayers,
                message: messageData
            })
        );

        emit BridgeERC721({
            sourceTokenAddress: requestBridgeERC721Info.sourceTokenAddress,
            destinationBlockchainID: requestBridgeERC721Info.destinationBlockchainID,
            teleporterMessageID: messageID,
            destinationBridgeAddress: requestBridgeERC721Info.destinationBridgeAddress,
            sender: requestBridgeERC721Info.sender,
            recipient: requestBridgeERC721Info.recipient,
            tokenIds: requestBridgeERC721Info.tokenIds
        });
    }

    function _processERC1155Mint(RequestBridgeERC1155Info memory requestBridgeERC1155Info) private {
        uint256 tokenLength = requestBridgeERC1155Info.tokenIds.length;
        uint256 requiredGas = tokenLength * MINT_BRIDGE_TOKENS_REQUIRED_GAS;
        require(requiredGas < 15000000, "SourceBridge/overBlockGas: too much tokens");
        require(
            tokenLength == requestBridgeERC1155Info.amounts.length,
            "SourceBridge/wrongLength: ids and amount length mismatch"
        );
        for (uint256 i; i < tokenLength; ) {
            ERC1155(requestBridgeERC1155Info.sourceTokenAddress).safeTransferFrom(
                requestBridgeERC1155Info.sender,
                address(this),
                requestBridgeERC1155Info.tokenIds[i],
                requestBridgeERC1155Info.amounts[i],
                ""
            );

            bridgedFts[requestBridgeERC1155Info.destinationBlockchainID][
                requestBridgeERC1155Info.destinationBridgeAddress
            ][requestBridgeERC1155Info.sourceTokenAddress][
                requestBridgeERC1155Info.tokenIds[i]
            ] += requestBridgeERC1155Info.amounts[i];

            unchecked {
                i++;
            }
        }

        bytes memory messageData = _encodeMintERC1155Data({
            originContractAddress: requestBridgeERC1155Info.sourceTokenAddress,
            recipient: requestBridgeERC1155Info.recipient,
            tokenIds: requestBridgeERC1155Info.tokenIds,
            bridgeAmounts: requestBridgeERC1155Info.amounts
        });

        ITeleporterMessenger teleporterMessenger = _getTeleporterMessenger();
        bytes32 messageID = teleporterMessenger.sendCrossChainMessage(
            TeleporterMessageInput({
                destinationBlockchainID: requestBridgeERC1155Info.destinationBlockchainID,
                destinationAddress: requestBridgeERC1155Info.destinationBridgeAddress,
                feeInfo: TeleporterFeeInfo({ feeTokenAddress: address(0), amount: 0 }),
                requiredGasLimit: requiredGas,
                allowedRelayerAddresses: _allowedRelayers,
                message: messageData
            })
        );

        emit BridgeERC1155({
            sourceTokenAddress: requestBridgeERC1155Info.sourceTokenAddress,
            destinationBlockchainID: requestBridgeERC1155Info.destinationBlockchainID,
            teleporterMessageID: messageID,
            destinationBridgeAddress: requestBridgeERC1155Info.destinationBridgeAddress,
            sender: requestBridgeERC1155Info.sender,
            recipient: requestBridgeERC1155Info.recipient,
            tokenIds: requestBridgeERC1155Info.tokenIds,
            amounts: requestBridgeERC1155Info.amounts
        });
    }
}
