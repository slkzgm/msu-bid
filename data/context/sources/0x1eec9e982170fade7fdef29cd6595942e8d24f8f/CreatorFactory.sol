

// Sources flattened with hardhat v2.22.6 https://hardhat.org

// SPDX-License-Identifier: MIT

// File @openzeppelin/contracts-upgradeable/utils/AddressUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library AddressUpgradeable {
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
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
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
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.0/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
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
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
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


// File @openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (proxy/utils/Initializable.sol)

pragma solidity ^0.8.2;

/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * The initialization functions use a version number. Once a version number is used, it is consumed and cannot be
 * reused. This mechanism prevents re-execution of each "step" but allows the creation of new initialization steps in
 * case an upgrade adds a module that needs to be initialized.
 *
 * For example:
 *
 * [.hljs-theme-light.nopadding]
 * ```solidity
 * contract MyToken is ERC20Upgradeable {
 *     function initialize() initializer public {
 *         __ERC20_init("MyToken", "MTK");
 *     }
 * }
 *
 * contract MyTokenV2 is MyToken, ERC20PermitUpgradeable {
 *     function initializeV2() reinitializer(2) public {
 *         __ERC20Permit_init("MyToken");
 *     }
 * }
 * ```
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {ERC1967Proxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 *
 * [CAUTION]
 * ====
 * Avoid leaving a contract uninitialized.
 *
 * An uninitialized contract can be taken over by an attacker. This applies to both a proxy and its implementation
 * contract, which may impact the proxy. To prevent the implementation contract from being used, you should invoke
 * the {_disableInitializers} function in the constructor to automatically lock it when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() {
 *     _disableInitializers();
 * }
 * ```
 * ====
 */
abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     * @custom:oz-retyped-from bool
     */
    uint8 private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Triggered when the contract has been initialized or reinitialized.
     */
    event Initialized(uint8 version);

    /**
     * @dev A modifier that defines a protected initializer function that can be invoked at most once. In its scope,
     * `onlyInitializing` functions can be used to initialize parent contracts.
     *
     * Similar to `reinitializer(1)`, except that functions marked with `initializer` can be nested in the context of a
     * constructor.
     *
     * Emits an {Initialized} event.
     */
    modifier initializer() {
        bool isTopLevelCall = !_initializing;
        require(
            (isTopLevelCall && _initialized < 1) || (!AddressUpgradeable.isContract(address(this)) && _initialized == 1),
            "Initializable: contract is already initialized"
        );
        _initialized = 1;
        if (isTopLevelCall) {
            _initializing = true;
        }
        _;
        if (isTopLevelCall) {
            _initializing = false;
            emit Initialized(1);
        }
    }

    /**
     * @dev A modifier that defines a protected reinitializer function that can be invoked at most once, and only if the
     * contract hasn't been initialized to a greater version before. In its scope, `onlyInitializing` functions can be
     * used to initialize parent contracts.
     *
     * A reinitializer may be used after the original initialization step. This is essential to configure modules that
     * are added through upgrades and that require initialization.
     *
     * When `version` is 1, this modifier is similar to `initializer`, except that functions marked with `reinitializer`
     * cannot be nested. If one is invoked in the context of another, execution will revert.
     *
     * Note that versions can jump in increments greater than 1; this implies that if multiple reinitializers coexist in
     * a contract, executing them in the right order is up to the developer or operator.
     *
     * WARNING: setting the version to 255 will prevent any future reinitialization.
     *
     * Emits an {Initialized} event.
     */
    modifier reinitializer(uint8 version) {
        require(!_initializing && _initialized < version, "Initializable: contract is already initialized");
        _initialized = version;
        _initializing = true;
        _;
        _initializing = false;
        emit Initialized(version);
    }

    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} and {reinitializer} modifiers, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    /**
     * @dev Locks the contract, preventing any future reinitialization. This cannot be part of an initializer call.
     * Calling this in the constructor of a contract will prevent that contract from being initialized or reinitialized
     * to any version. It is recommended to use this to lock implementation contracts that are designed to be called
     * through proxies.
     *
     * Emits an {Initialized} event the first time it is successfully executed.
     */
    function _disableInitializers() internal virtual {
        require(!_initializing, "Initializable: contract is initializing");
        if (_initialized != type(uint8).max) {
            _initialized = type(uint8).max;
            emit Initialized(type(uint8).max);
        }
    }

    /**
     * @dev Returns the highest version that has been initialized. See {reinitializer}.
     */
    function _getInitializedVersion() internal view returns (uint8) {
        return _initialized;
    }

    /**
     * @dev Returns `true` if the contract is currently initializing. See {onlyInitializing}.
     */
    function _isInitializing() internal view returns (bool) {
        return _initializing;
    }
}


// File @openzeppelin/contracts-upgradeable/utils/ContextUpgradeable.sol@v4.9.2

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
abstract contract ContextUpgradeable is Initializable {
    function __Context_init() internal onlyInitializing {
    }

    function __Context_init_unchained() internal onlyInitializing {
    }
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/metatx/ERC2771ContextUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.7.0) (metatx/ERC2771Context.sol)

pragma solidity ^0.8.9;


/**
 * @dev Context variant with ERC2771 support.
 */
abstract contract ERC2771ContextUpgradeable is Initializable, ContextUpgradeable {
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

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/utils/introspection/IERC165Upgradeable.sol@v4.9.2

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
interface IERC165Upgradeable {
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


// File @openzeppelin/contracts-upgradeable/token/ERC1155/IERC1155ReceiverUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC1155/IERC1155Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @dev _Available since v3.1._
 */
interface IERC1155ReceiverUpgradeable is IERC165Upgradeable {
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


// File @openzeppelin/contracts-upgradeable/utils/introspection/ERC165Upgradeable.sol@v4.9.2

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
abstract contract ERC165Upgradeable is Initializable, IERC165Upgradeable {
    function __ERC165_init() internal onlyInitializing {
    }

    function __ERC165_init_unchained() internal onlyInitializing {
    }
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165Upgradeable).interfaceId;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/token/ERC1155/utils/ERC1155ReceiverUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC1155/utils/ERC1155Receiver.sol)

pragma solidity ^0.8.0;



/**
 * @dev _Available since v3.1._
 */
abstract contract ERC1155ReceiverUpgradeable is Initializable, ERC165Upgradeable, IERC1155ReceiverUpgradeable {
    function __ERC1155Receiver_init() internal onlyInitializing {
    }

    function __ERC1155Receiver_init_unchained() internal onlyInitializing {
    }
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override(ERC165Upgradeable, IERC165Upgradeable) returns (bool) {
        return interfaceId == type(IERC1155ReceiverUpgradeable).interfaceId || super.supportsInterface(interfaceId);
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/token/ERC1155/utils/ERC1155HolderUpgradeable.sol@v4.9.2

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
contract ERC1155HolderUpgradeable is Initializable, ERC1155ReceiverUpgradeable {
    function __ERC1155Holder_init() internal onlyInitializing {
    }

    function __ERC1155Holder_init_unchained() internal onlyInitializing {
    }
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

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/token/ERC721/IERC721ReceiverUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC721/IERC721Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @title ERC721 token receiver interface
 * @dev Interface for any contract that wants to support safeTransfers
 * from ERC721 asset contracts.
 */
interface IERC721ReceiverUpgradeable {
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


// File @openzeppelin/contracts-upgradeable/token/ERC721/utils/ERC721HolderUpgradeable.sol@v4.9.2

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (token/ERC721/utils/ERC721Holder.sol)

pragma solidity ^0.8.0;


/**
 * @dev Implementation of the {IERC721Receiver} interface.
 *
 * Accepts all token transfers.
 * Make sure the contract is able to use its token with {IERC721-safeTransferFrom}, {IERC721-approve} or {IERC721-setApprovalForAll}.
 */
contract ERC721HolderUpgradeable is Initializable, IERC721ReceiverUpgradeable {
    function __ERC721Holder_init() internal onlyInitializing {
    }

    function __ERC721Holder_init_unchained() internal onlyInitializing {
    }
    /**
     * @dev See {IERC721Receiver-onERC721Received}.
     *
     * Always returns `IERC721Receiver.onERC721Received.selector`.
     */
    function onERC721Received(address, address, uint256, bytes memory) public virtual override returns (bytes4) {
        return this.onERC721Received.selector;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


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


// File @projecta/min-proxy/contracts/gen/MinBeaconProxy.sol@v0.1.1

/* Autogenerated file. Do not edit manually. */
/* solhint-disable */
// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.18;

library MinBeaconProxyGetCode {
    function getCode(address beacon) internal pure returns (bytes memory) {
        return abi.encodePacked("`E\x80`\t=9=\xf3c\\`\xda\x1b=R===6==6==` =`\x04`\x1cs", beacon, "Z\xfa`2W\xfd[Q\x927Z\xf4=\x82\x80>\x90=\x91`CW\xfd[\xf3");
    }
}


// File @projecta/min-proxy/contracts/gen/MinProxy.sol@v0.1.1

/* Autogenerated file. Do not edit manually. */
/* solhint-disable */
// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.18;

library MinProxyGetCode {
    function getCode(address impl) internal pure returns (bytes memory) {
        return abi.encodePacked("`-\x80`\t=9=\xf36==7===6=s", impl, "Z\xf4=\x82\x80>\x90=\x91`+W\xfd[\xf3");
    }
}


// File @projecta/min-proxy/contracts/MinProxy.sol@v0.1.1

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.18;


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


// File @projecta/multisig-contracts/common/SelfCallUpgradeable.sol@v0.6.5

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.17;


/**
 * @title SelfCallUpgradeable -  Validates the sender address during self-calls of the contract.
 */
contract SelfCallUpgradeable is Context, Initializable {
    /* solhint-disable-next-line func-name-mixedcase */
    function __SelfCall_init() internal onlyInitializing {
        __SelfCall_init_unchained();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __SelfCall_init_unchained() internal onlyInitializing {}

    modifier isSelfCall() {
        require(_msgSender() == address(this), "SelfCallUpgradeable/forbidden: caller is not this contract");
        _;
    }

    uint256[50] private __gap;
}


// File @projecta/multisig-contracts/access/ExecutorManagerUpgradeable.sol@v0.6.5

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.17;

/**
 * @title ExecutorManagerUpgradeable - Manages executors for a multisig contract.
 * @notice This contract provides functionalities for managing the list of executor
 *         who can generate or execute(cancel) transaction in multisig contract.
 */



contract ExecutorManagerUpgradeable is Context, Initializable, SelfCallUpgradeable {
    mapping(address => bool) private _isExecutor;

    event ExecutorGranted(address indexed account);
    event ExecutorRevoked(address indexed account);

    /* solhint-disable-next-line func-name-mixedcase */
    function __ExecutorManager_init() internal onlyInitializing {
        __ExecutorManager_init_unchained();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __ExecutorManager_init_unchained() internal onlyInitializing {
        _isExecutor[_msgSender()] = true;
    }

    /**
     * @notice Grants executor privilege to `account`.
     * @dev Callable only via self call.
     * @param account Address to be granted executor privilege.
     */
    function grantExecutor(address account) external virtual isSelfCall {
        _grantExecutor(account);
    }

    /**
     * @notice Revokes executor privilege from `account`.
     * @dev Callable only via self call.
     * @param account Address to be revoked executor privilege.
     */
    function revokeExecutor(address account) external isSelfCall {
        require(
            isExecutor(account),
            "ExecutorManagerUpgradeable/revokeExecutorConflict: account is already a non-executor"
        );
        _isExecutor[account] = false;

        emit ExecutorRevoked(account);
    }

    /**
     * @notice Returns if `account` is an executor.
     * @return Boolean if `account` is an executor.
     */
    function isExecutor(address account) public view returns (bool) {
        return _isExecutor[account];
    }

    /**
     * @notice Grants executor privilege to `account`.
     * @dev Can specify conditions for the `account` by override this function.
     * @param account Address to be granted executor privilege.
     */
    function _grantExecutor(address account) internal virtual {
        require(
            !isExecutor(account),
            "ExecutorManagerUpgradeable/grantExecutorConflict: account is already an executor"
        );
        _isExecutor[account] = true;

        emit ExecutorGranted(account);
    }

    uint256[49] private __gap;
}


// File @openzeppelin/contracts/utils/structs/EnumerableSet.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/structs/EnumerableSet.sol)
// This file was procedurally generated from scripts/generate/templates/EnumerableSet.js.

pragma solidity ^0.8.0;

/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 *
 * ```
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * As of v3.3.0, sets of type `bytes32` (`Bytes32Set`), `address` (`AddressSet`)
 * and `uint256` (`UintSet`) are supported.
 *
 * [WARNING]
 * ====
 * Trying to delete such a structure from storage will likely result in data corruption, rendering the structure
 * unusable.
 * See https://github.com/ethereum/solidity/pull/11843[ethereum/solidity#11843] for more info.
 *
 * In order to clean an EnumerableSet, you can either remove all elements one by one or create a fresh instance using an
 * array of EnumerableSet.
 * ====
 */
library EnumerableSet {
    // To implement this library for multiple types with as little code
    // repetition as possible, we write it in terms of a generic Set type with
    // bytes32 values.
    // The Set implementation uses private functions, and user-facing
    // implementations (such as AddressSet) are just wrappers around the
    // underlying Set.
    // This means that we can only create new EnumerableSets for types that fit
    // in bytes32.

    struct Set {
        // Storage of set values
        bytes32[] _values;
        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping(bytes32 => uint256) _indexes;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) {
            // Equivalent to contains(set, value)
            // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
            // the array, and then remove the last element (sometimes called as 'swap and pop').
            // This modifies the order of the array, as noted in {at}.

            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            if (lastIndex != toDeleteIndex) {
                bytes32 lastValue = set._values[lastIndex];

                // Move the last value to the index where the value to delete is
                set._values[toDeleteIndex] = lastValue;
                // Update the index for the moved value
                set._indexes[lastValue] = valueIndex; // Replace lastValue's index to valueIndex
            }

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function _values(Set storage set) private view returns (bytes32[] memory) {
        return set._values;
    }

    // Bytes32Set

    struct Bytes32Set {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(Bytes32Set storage set) internal view returns (bytes32[] memory) {
        bytes32[] memory store = _values(set._inner);
        bytes32[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(AddressSet storage set) internal view returns (address[] memory) {
        bytes32[] memory store = _values(set._inner);
        address[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(UintSet storage set) internal view returns (uint256[] memory) {
        bytes32[] memory store = _values(set._inner);
        uint256[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }
}


// File @projecta/multisig-contracts/access/OwnerManagerUpgradeable.sol@v0.6.5

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.17;




/**
 * @title OwnerManagerUpgradeable - Manages owners and threshold for a multisig contract.
 * @notice This contract provides functionalities for managing the list of owners who can sign transactions
 *         and sets the required threshold of confirmations for executing transactions.
 * @dev Implement `_owners` using {EnumerableSet.AddressSet} to ensure uniqueness,
 *      efficient iteration, improved gas efficiency, and more.
 */
contract OwnerManagerUpgradeable is Context, Initializable, SelfCallUpgradeable {
    using EnumerableSet for EnumerableSet.AddressSet;

    EnumerableSet.AddressSet private _owners;

    uint256 private _threshold;

    event OwnerAdded(address indexed newOwner);
    event OwnerRemoved(address indexed previousOwner);
    event ThresholdChanged(uint256 indexed newThreshold);

    modifier onlyOwner() {
        require(_owners.contains(_msgSender()), "OwnerManagerUpgradeable/ownerForbidden: caller is not the owner");
        _;
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __OwnerManager_init(address[] memory owners_, uint256 threshold_) internal onlyInitializing {
        __OwnerManager_init_unchained(owners_, threshold_);
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __OwnerManager_init_unchained(address[] memory owners_, uint256 threshold_) internal onlyInitializing {
        require(owners_.length > 0, "OwnerManagerUpgradeable/invalidRequest: owners required");
        require(
            threshold_ <= owners_.length,
            "OwnerManagerUpgradeable/invalidThreshold: threshold must be less than or equal to length of owners"
        );

        _threshold = threshold_;

        for (uint256 i = 0; i < owners_.length; i++) {
            _addOwner(owners_[i]);
        }
    }

    /**
     * @notice Adds the owner.
     * @dev Callable only via self call.
     * @param newOwner New owner address to add.
     */
    function addOwner(address newOwner) external isSelfCall {
        _beforeUpdateOwner();
        _addOwner(newOwner);
    }

    /**
     * @notice Adds the owner and updates threshold with `newThreshold`.
     * @dev Callable only via self call.
     * @param newOwner New owner address to add.
     * @param newThreshold New threshold to update.
     */
    function addOwnerWithNewThreshold(address newOwner, uint256 newThreshold) external isSelfCall {
        _beforeUpdateOwner();
        _addOwner(newOwner);
        _changeThreshold(newThreshold);
    }

    /**
     * @notice Removes the owner.
     * @dev Callable only via self call.
     * @param ownerToRemove Owner address to remove.
     */
    function removeOwner(address ownerToRemove) external isSelfCall {
        require(
            _owners.length() - 1 >= _threshold,
            "OwnerManagerUpgradeable/invalidThreshold: threshold must be less than or equal to length of owners"
        );
        _beforeUpdateOwner();
        _removeOwner(ownerToRemove);
    }

    /**
     * @notice Removes the owner and updates threshold with `newThreshold`.
     * @dev Callable only via self call.
     * @param ownerToRemove Owner address to remove.
     * @param newThreshold New threshold to update.
     */
    function removeOwnerWithNewThreshold(address ownerToRemove, uint256 newThreshold) external isSelfCall {
        require(
            _owners.length() - 1 >= newThreshold,
            "OwnerManagerUpgradeable/invalidThreshold: threshold must be less than or equal to length of owners"
        );
        _beforeUpdateOwner();
        _removeOwner(ownerToRemove);
        _changeThreshold(newThreshold);
    }

    /**
     * @notice Changes the owner.
     * @dev Callable only via self call.
     * @param prevOwner Previous owner address to remove.
     * @param newOwner New Owner address to add.
     */
    function changeOwner(address prevOwner, address newOwner) external isSelfCall {
        _beforeUpdateOwner();
        _changeOwner(prevOwner, newOwner);
    }

    /**
     * @notice Changes the owner and updates threshold with `newThreshold`.
     * @dev Callable only via self call.
     * @param prevOwner Previous owner address to remove.
     * @param newOwner New Owner address to add.
     * @param newThreshold New threshold to update.
     */
    function changeOwnerWithNewThreshold(
        address prevOwner,
        address newOwner,
        uint256 newThreshold
    ) external isSelfCall {
        _beforeUpdateOwner();
        _changeOwner(prevOwner, newOwner);
        _changeThreshold(newThreshold);
    }

    /**
     * @notice Updates threshold with `newThreshold`.
     * @dev Callable only via self call.
     * @param newThreshold New threshold to update.
     */
    function changeThreshold(uint256 newThreshold) external isSelfCall {
        _beforeUpdateOwner();
        _changeThreshold(newThreshold);
    }

    /**
     * @notice Returns a list owners.
     * @return Array of owners.
     */
    function getAllOwners() external view returns (address[] memory) {
        return _owners.values();
    }

    /**
     * @notice Returns owner that index `idx`.
     * @return Array of Safe owners.
     */
    function getOwner(uint256 idx) external view returns (address) {
        return _owners.at(idx);
    }

    /**
     * @notice Returns count of owners.
     * @return Owner count number.
     */
    function getOwnerCount() external view returns (uint256) {
        return _owners.length();
    }

    /**
     * @notice Returns current Threshold.
     * @return Threshold number.
     */
    function threshold() public view returns (uint256) {
        return _threshold;
    }

    /**
     * @notice Returns if `account` is an owner address.
     * @return Boolean if `account` is an owner address.
     */
    function isOwner(address account) public view returns (bool) {
        return _owners.contains(account);
    }

    /**
     * @notice Prevents adding executor addresses as owners.
     * @dev Can specify conditions for the `newOwner` by override this function.
     * @param newOwner Address of the new owner.
     */
    function _addOwner(address newOwner) internal virtual {
        require(newOwner != address(0), "OwnerManagerUpgradeable/invalidAddress: zero address can not be owner");
        require(_owners.add(newOwner), "OwnerManagerUpgradeable/invalidOwner: newOwner is already an owner");

        emit OwnerAdded(newOwner);
    }

    /**
     * @notice Prevents adding executor addresses as owners.
     * @param ownerToRemove Address of the new owner.
     */
    function _removeOwner(address ownerToRemove) internal {
        require(_owners.remove(ownerToRemove), "OwnerManagerUpgradeable/invalidOwner: ownerToRemove is not owner");

        emit OwnerRemoved(ownerToRemove);
    }

    /**
     * @notice Changes the owner.
     * @dev Callable only via self call.
     * @param prevOwner Previous owner address to be removed.
     * @param newOwner New Owner address to be added.
     */
    function _changeOwner(address prevOwner, address newOwner) internal {
        require(prevOwner != newOwner, "OwnerManagerUpgradeable/invalidOwner: prevOwner and newOwner is same address");
        _addOwner(newOwner);
        _removeOwner(prevOwner);
    }

    /**
     * @notice Changes the threshold.
     * @dev Callable only via self call.
     * @param newThreshold New threshold to be updated.
     */
    function _changeThreshold(uint256 newThreshold) internal {
        require(
            newThreshold >= 1,
            "OwnerManagerUpgradeable/invalidThreshold: newThreshold must be higher than or equal to 1"
        );
        require(
            _owners.length() >= newThreshold,
            "OwnerManagerUpgradeable/invalidThreshold: threshold must be less than or equal to length of owners"
        );
        _threshold = newThreshold;

        emit ThresholdChanged(newThreshold);
    }

    function _beforeUpdateOwner() internal virtual {}

    uint256[48] private __gap;
}


// File @projecta/multisig-contracts/common/TokenHolderUpgradeable.sol@v0.6.5

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.17;



/**
 * @title TokenHolderUpgradeable - Implement {ERC721Holder} and {ERC1155Holder} to accept all token transfer
 */
contract TokenHolderUpgradeable is Initializable, ERC721HolderUpgradeable, ERC1155HolderUpgradeable {
    /* solhint-disable-next-line func-name-mixedcase */
    function __TokenHolder_init() internal onlyInitializing {
        __TokenHolder_init_unchained();
        __ERC721Holder_init_unchained();
        __ERC1155Holder_init_unchained();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __TokenHolder_init_unchained() internal onlyInitializing {}

    receive() external payable {}

    uint256[50] private __gap;
}


// File @projecta/multisig-contracts/MultisigUpgradeable.sol@v0.6.5

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.17;





/**
 * @title MultisigUpgradeable - A multisignature contract that using on-chain signature.
 * @dev Main features:
 *      - Executors: List of addresses that can create, execute, or cancel transaction requests.
 *      - Owners: List of addresses that can sign transactions, including those with executor privileges.
 *        Owners can sign transactions directly by calling {signTransaction}.
 *      - Threshold: Number of required confirmations to execute a transaction.
 *      - Transaction Status: Transaction requests are managed step by step on-chain.
 *      - Transaction Request : Manages transactions with TransactionRequest struct.
 *        It allows signing multiple transactions at once.
 *      - Sequence : Id of the transaction request.
 *      - TokenHolder: Includes functions related to token transfers.
 */
contract MultisigUpgradeable is Context, OwnerManagerUpgradeable, ExecutorManagerUpgradeable, TokenHolderUpgradeable {
    enum Status {
        UNDEFINED,
        GENERATED,
        CANCELLED,
        EXECUTED
    }

    struct Transaction {
        address to;
        uint256 value;
        uint256 gas;
        bytes data;
    }

    struct TransactionRequest {
        address requester;
        uint16 signedCount;
        Status txStatus;
        Transaction[] transactions;
    }

    TransactionRequest[] private _transactionRequests;
    mapping(uint256 => mapping(address => bool)) private _isSigned;
    uint256 private _ownerUpdatedSequence;

    event GenerateTransaction(uint256 indexed sequence, address indexed requester, Transaction[] transactions);
    event SignTransaction(uint256 indexed sequence, address indexed account);
    event CancelTransaction(uint256 indexed sequence);
    event ExecuteTransaction(uint256 indexed sequence);

    /* solhint-disable-next-line func-name-mixedcase */
    function __Multisig_init(address[] memory owners_, uint256 threshold_) internal onlyInitializing {
        __TokenHolder_init();
        __ExecutorManager_init();
        __OwnerManager_init(owners_, threshold_);
        __Multisig_init_unchained();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __Multisig_init_unchained() internal onlyInitializing {}

    modifier onlyAtLeastExecutor() {
        require(
            isExecutor(_msgSender()) || isOwner(_msgSender()),
            "MultisigUpgradeable/executorForbidden: caller is neither the owner nor an executor"
        );
        _;
    }

    modifier onlyRequester(uint256 sequence) {
        require(
            _transactionRequests[sequence].requester == _msgSender(),
            "MultisigUpgradeable/requesterForbidden: caller is not a requester"
        );
        _;
    }

    modifier onlyTransactionGenerated(uint256 sequence) {
        require(
            _transactionRequests[sequence].txStatus == Status.GENERATED,
            "MultisigUpgradeable/invalidSequence: not in generated state"
        );
        _;
    }

    modifier whenTransactionExists(uint256 sequence) {
        require(sequence < _transactionRequests.length, "MultisigUpgradeable/invalidSequence: nonexistent sequence");
        _;
    }

    modifier isValidSequence(uint256 sequence) {
        require(sequence >= _ownerUpdatedSequence, "MultisigUpgradeable/invalidSequence: expired sequence");
        _;
    }

    /**
     * @notice Generates transaction request.
     * @param to The target address where the transaction will be sent.
     * @param value The amount of native tokens to be sent in the transaction.
     * @param gas The maximum amount of gas to be used for the transaction.
     * @param data The data payload of the transaction.
     * @return sequence The id of the transaction request.
     */
    function generateTransaction(
        address to,
        uint256 value,
        uint256 gas,
        bytes calldata data
    ) external onlyAtLeastExecutor returns (uint256 sequence) {
        Transaction[] memory transactions = new Transaction[](1);
        transactions[0] = Transaction({ to: to, value: value, gas: gas, data: data });

        return _generateTransaction(transactions);
    }

    /**
     * @notice Generates multiple transaction requests.
     * @param transactions list of the transaction data that contains `to`, `value`, `gas, `data`.
     * @return sequence The id of the transaction request.
     */
    function generateTransactions(
        Transaction[] calldata transactions
    ) external onlyAtLeastExecutor returns (uint256 sequence) {
        return _generateTransaction(transactions);
    }

    /**
     * @notice Cancels transaction requests
     * @param sequence The id of the transaction request.
     */
    function cancelTransaction(
        uint256 sequence
    ) external whenTransactionExists(sequence) onlyTransactionGenerated(sequence) onlyRequester(sequence) {
        _transactionRequests[sequence].txStatus = Status.CANCELLED;

        emit CancelTransaction(sequence);
    }

    /**
     * @notice Signs transaction request.
     * @param sequence The id of the transaction request.
     */
    function signTransaction(
        uint256 sequence
    ) external onlyOwner whenTransactionExists(sequence) onlyTransactionGenerated(sequence) isValidSequence(sequence) {
        require(!_isSigned[sequence][_msgSender()], "MultisigUpgradeable/invalidRequest: already signed");
        _isSigned[sequence][_msgSender()] = true;
        _transactionRequests[sequence].signedCount++;

        emit SignTransaction(sequence, _msgSender());
    }

    /**
     * @notice Executes transaction request.
     * @param sequence The id of the transaction request.
     */
    function executeTransaction(
        uint256 sequence
    )
        external
        whenTransactionExists(sequence)
        onlyTransactionGenerated(sequence)
        onlyRequester(sequence)
        isValidSequence(sequence)
    {
        require(
            _transactionRequests[sequence].signedCount >= threshold(),
            "MultisigUpgradeable/executeForbidden: not all signed yet"
        );
        _transactionRequests[sequence].txStatus = Status.EXECUTED;

        Transaction[] memory transactions = _transactionRequests[sequence].transactions;
        uint256 accumulatedGas = 0;
        for (uint i = 0; i < transactions.length; ) {
            // solhint-disable-next-line avoid-low-level-calls
            (bool success, bytes memory returnData) = transactions[i].to.call{
                gas: transactions[i].gas,
                value: transactions[i].value
            }(transactions[i].data);
            Address.verifyCallResult(success, returnData, "MultisigUpgradeable/revert: transaction failed");
            accumulatedGas += transactions[i].gas;

            unchecked {
                i++;
            }
        }

        if (gasleft() <= accumulatedGas / 63) {
            // solhint-disable-next-line no-inline-assembly
            assembly {
                invalid()
            }
        }

        emit ExecuteTransaction(sequence);
    }

    /**
     * @notice Retrieve the current status of a transaction request.
     * @dev Transaction requests have different states:
     *      - UNDEFINED: Default value when the request is not created.
     *      - GENERATED: Value when the request is created.
     *      - EXECUTED or CANCELLED: Value when the request is executed(canceled).
     * @param sequence The ID of the transaction request
     * @return current status of transaction request as a Status enum.
     */
    function txStatus(uint256 sequence) external view whenTransactionExists(sequence) returns (Status) {
        return _transactionRequests[sequence].txStatus;
    }

    /**
     * @notice Generates multiple transaction requests.
     * @param transactions list of the transaction data that contains `to`, `value`, `gas, `data`.
     * @return sequence The id of the transaction request.
     */
    function _generateTransaction(Transaction[] memory transactions) internal returns (uint256 sequence) {
        _beforeGenerateTransaction(transactions);
        _transactionRequests.push();
        unchecked {
            sequence = _getSequence();
            TransactionRequest storage transactionRequest = _transactionRequests[sequence];
            transactionRequest.requester = _msgSender();
            transactionRequest.signedCount = 0;
            transactionRequest.txStatus = Status.GENERATED;
            uint size = transactions.length;
            for (uint i = 0; i < size; i++) {
                require(
                    transactions[i].to != address(0),
                    "MultisigUpgradeable/invalidAddress: transaction to zero address"
                );
                transactionRequest.transactions.push(transactions[i]);
            }
            emit GenerateTransaction(sequence, _msgSender(), transactions);
        }
    }

    /**
     * @notice See {OwnerManagerUpgradeable-_addOwner}.
     * @dev Overriden {OwnerManagerUpgradeable-_addOwner} to prevent adding executor address as owner.
     */
    function _addOwner(address newOwner) internal override {
        require(!isExecutor(newOwner), "MultisigUpgradeable/invalidAddress: newOwner is Executor");
        super._addOwner(newOwner);
    }

    /**
     * @notice See {ExecutorManagerUpgradeable-_grantExecutor}.
     * @dev Overriden {ExecutorManagerUpgradeable-_grantExecutor} to prevent adding owner address as executor.
     */
    function _grantExecutor(address account) internal override {
        require(!isOwner(account), "MultisigUpgradeable/invalidAddress: new executor is owner");
        super._grantExecutor(account);
    }

    /**
     * @dev Hook that is called before generate transaction request.
     */
    function _beforeGenerateTransaction(Transaction[] memory transactions) internal virtual {}

    /**
     * @dev Hook that is called when owner is updated.
     */
    function _beforeUpdateOwner() internal virtual override {
        _ownerUpdatedSequence = _getSequence() + 1;
    }

    /**
     * @notice Return count of transactionRequest.
     * @return current sequence number.
     */
    function _getSequence() internal view returns (uint) {
        return _transactionRequests.length - 1;
    }

    uint256[50] private __gap;
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


// File contracts/Creator/interfaces/INextMeso.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;

/// @notice NextMeso token(ERC20) for maplestory
interface INextMeso {
    function withdraw(uint256 amount) external;
}


// File contracts/Creator/utils/CreatorTokenControllerUpgradeable.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;



/// @title CreatorTokenControllerUpgradeable - A Contract to manage the amount of withdrawable and non-withdrawable tokens
abstract contract CreatorTokenControllerUpgradeable is Initializable {
    using SafeERC20 for IERC20;

    /// @notice Emitted when the creator balance is updated
    /// @param creatorAddress Creator address
    /// @param balance Creator target ERC20 balance
    event CreatorBalanceUpdated(address indexed creatorAddress, uint256 balance);

    /* solhint-disable-next-line func-name-mixedcase */
    function __CreatorTokenController_init() internal onlyInitializing {
        __CreatorTokenController_init_unchained();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __CreatorTokenController_init_unchained() internal onlyInitializing {}

    /// @notice Withdraw ERC20 token
    function withdrawERC20(IERC20 token, address account, uint256 amount) external virtual;

    /// @notice Allocate ERC20 token
    function allocateERC20(IERC20 token, address account, uint256 amount) external virtual;

    /// @notice Withdraws the withdrawable amount
    /// @param token ERC20 token address to withdraw
    /// @param account Recipient address
    /// @param amount Amount of ERC20 token
    function _withdrawERC20(IERC20 token, address account, uint256 amount) internal {
        token.safeTransfer(account, amount);
    }

    /// @notice Allocate ERC20 token
    /// @dev Allocate is possible for all types of assets (withdrawable and non-withdrawable)
    /// @param token ERC20 token address to allocate
    /// @param account Recipient address
    /// @param amount Amount of ERC20 token
    function _allocateERC20(IERC20 token, address account, uint256 amount) internal {
        token.safeTransfer(account, amount);
    }

    uint256[49] private __gap;
}


// File contracts/Creator/CreatorWallet/CreatorWalletLogicUpgradeable.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;










/// @title CreatorWalletLogicUpgradeable - A contract that defines the functions that CreatorWallet can call
/// @dev Main feature
///      - allocate various assets (ERC20, ERC721, ERC1155) to DAppWallet or withdraw them externally
///      - send a request to ItemIssuance to issue an item
///      - Upgradeable: The administrator can add functions that the creator can use.
contract CreatorWalletLogicUpgradeable is Initializable, SelfCallUpgradeable, CreatorTokenControllerUpgradeable {
    using SafeERC20 for IERC20;

    /// @notice MSU currency
    INextMeso public immutable nextMeso;

    /// @notice CreatorFactory contract
    ICreatorFactory public immutable creatorFactory;

    /// @notice Emitted when the creator allocates items(ERC721, ERC1155) to the dApp
    /// @param dAppId A id of dApp
    /// @param hashedData A hashed data of items(Due to the large size of the data, it is stored as a hash value)
    event ItemsAllocated(uint32 dAppId, bytes hashedData);

    /// @dev Check if dAppId is owned by this creator
    /// @param dAppId A id of dApp
    modifier onlyOwnedDApp(uint32 dAppId) {
        require(
            creatorFactory.creatorIdOfDApp(dAppId) == creatorId(),
            "CreatorWalletLogicUpgradeable/forbidden: The dApp is not owned by the creator"
        );
        require(
            creatorFactory.isActiveDApp(dAppId),
            "CreatorWalletLogicUpgradeable/inactiveDApp: given an inactive id"
        );
        _;
    }

    modifier validAddress(address addr) {
        require(addr != address(0), "CreatorWalletLogicUpgradeable/validAddress: couldn't be zero address");
        _;
    }

    /// @dev Set the values of {creatorFactory}.
    constructor(
        INextMeso nextMeso_,
        ICreatorFactory creatorFactory_
    ) validAddress(address(nextMeso_)) validAddress(address(creatorFactory_)) {
        nextMeso = nextMeso_;
        creatorFactory = creatorFactory_;
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __CreatorWalletLogic_init() internal onlyInitializing {
        __CreatorWalletLogic_init_unchained();
        __CreatorTokenController_init_unchained();
        __SelfCall_init();
    }

    /* solhint-disable-next-line func-name-mixedcase */
    function __CreatorWalletLogic_init_unchained() internal onlyInitializing {}

    /// @notice Allocate ERC20 tokens to creator-owned dapp accounts
    /// @param token A address of ERC20 token
    /// @param dAppId A id of dApp
    /// @param amount A amount of ERC20 token
    function allocateERC20(IERC20 token, uint32 dAppId, uint256 amount) external isSelfCall onlyOwnedDApp(dAppId) {
        _allocateERC20(token, creatorFactory.dAppAddress(dAppId), amount);
    }

    /// @notice Allocate ERC20 tokens to creator-owned dapp accounts
    /// @param token A address of ERC20 token
    /// @param dAppAddress A address of dApp
    /// @param amount A amount of ERC20 token
    function allocateERC20(
        IERC20 token,
        address dAppAddress,
        uint256 amount
    ) external override isSelfCall onlyOwnedDApp(creatorFactory.dAppId(dAppAddress)) {
        _allocateERC20(token, creatorFactory.dAppAddress(creatorFactory.dAppId(dAppAddress)), amount);
    }

    /// @notice Records the allocation of items with their hashed data to creator-owned dapp accounts
    /// @param dAppId A id of dApp
    /// @param hashedData A hashed data of items
    function allocateItems(uint32 dAppId, bytes memory hashedData) external isSelfCall onlyOwnedDApp(dAppId) {
        emit ItemsAllocated(dAppId, hashedData);
    }

    /// @notice Withdraw ERC20 tokens to external accounts
    /// @param token A address of ERC20 token
    /// @param account A address of account of recipient
    /// @param amount A amount of ERC20 token
    function withdrawERC20(IERC20 token, address account, uint256 amount) external override isSelfCall {
        _withdrawERC20(token, account, amount);
    }

    /// @notice Transfer native token to any address
    /// @param to A address of recipient
    /// @param amount Value to send
    function transferNXPC(address to, uint256 amount) external isSelfCall {
        (bool success, ) = to.call{ value: amount }("");
        require(success, "CreatorWalletLogicUpgradeable/invalidAmount: failed to transfer NXPC");
    }

    /// @notice Exchange nextMeso to NXPC
    /// @param amount Value to send
    function convertNesoToNXPC(uint256 amount) external isSelfCall {
        nextMeso.withdraw(amount);
    }

    /// @notice Transfer ERC721 token to any address
    /// @param token A address of ERC721 token
    /// @param to A address of recipient
    /// @param tokenId A id of ERC721 token
    function transferERC721(address token, address to, uint256 tokenId) external isSelfCall {
        IERC721(token).safeTransferFrom(address(this), to, tokenId);
    }

    /// @notice Batch function of {tansferERC721}
    function batchTransferERC721(
        address token,
        address[] calldata to,
        uint256[] calldata tokenIds
    ) external isSelfCall {
        require(
            to.length == tokenIds.length,
            "CreatorWalletLogicUpgradeable/invalidLength: length of to and tokenIds must be same"
        );
        uint256 toLength = to.length;
        for (uint256 i; i < toLength; i++) {
            IERC721(token).safeTransferFrom(address(this), to[i], tokenIds[i]);
        }
    }

    /// @notice Transfer ERC1155 token to any address
    /// @param token A address of ERC1155 token
    /// @param to A address of recipient
    /// @param id A id of ERC1155 token
    /// @param amount A amount of ERC1155 token
    function transferERC1155(address token, address to, uint256 id, uint256 amount) external isSelfCall {
        IERC1155(token).safeTransferFrom(address(this), to, id, amount, "");
    }

    /// @notice Batch function of {transferERC1155}
    function batchTransferERC1155(
        address token,
        address to,
        uint256[] calldata ids,
        uint256[] calldata amounts
    ) external isSelfCall {
        IERC1155(token).safeBatchTransferFrom(address(this), to, ids, amounts, "");
    }

    /// @notice Request to issue an item
    /// @param universe A id of universe
    /// @param itemAmount A amount of item to issue
    /// @param basketAmount A amount of basket
    function requestItemIssuance(uint24 universe, uint96 itemAmount, uint256 basketAmount) external isSelfCall {
        ItemIssuance itemIssuance = creatorFactory.itemIssuance();
        uint256 requireNXPC = itemIssuance.expectAmount(universe, itemAmount);
        itemIssuance.requestItemIssuance{ value: requireNXPC }(universe, itemAmount, basketAmount);
    }

    /// @notice Get the creator id of this contract
    function creatorId() public view returns (uint32) {
        return creatorFactory.creatorId(address(this));
    }

    uint256[50] private __gap;
}


// File contracts/Creator/CreatorWallet/CreatorWallet.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;






/// @title CreatorWallet - The multisig wallet used by the creator for the creator activity
/// @dev Main feature
///      - multisig: This contract is a multisig wallet
///      - CreatorWalletLogicUpgradeable: The functions that this contract can send are defined.
contract CreatorWallet is ERC2771ContextUpgradeable, MultisigUpgradeable, CreatorWalletLogicUpgradeable {
    constructor(
        address trustedForwarder_,
        INextMeso nextMeso_,
        ICreatorFactory creatorFactory_
    ) ERC2771ContextUpgradeable(trustedForwarder_) CreatorWalletLogicUpgradeable(nextMeso_, creatorFactory_) {
        _disableInitializers();
    }

    function initialize(address[] memory owners_, uint256 threshold_) external initializer {
        __Multisig_init(owners_, threshold_);
        __CreatorWalletLogic_init();
    }

    /// @notice To use only the functions in CreatorWalletLogicUpgradeable, only allow transactions to be sent to the self address.
    function _beforeGenerateTransaction(Transaction[] memory transactions) internal view override {
        uint256 transactionsLength = transactions.length;
        for (uint i = 0; i < transactionsLength; ) {
            require(transactions[i].to == address(this), "CreatorWallet/invalidTo: to address must be a self");
            unchecked {
                i++;
            }
        }
    }

    /// @notice See {ERC2771ContextUpgradeable-_msgSender}.
    function _msgSender() internal view virtual override(Context, ERC2771ContextUpgradeable) returns (address sender) {
        return ERC2771ContextUpgradeable._msgSender();
    }

    /// @notice See {ERC2771ContextUpgradeable-_msgData}.
    function _msgData() internal view virtual override(Context, ERC2771ContextUpgradeable) returns (bytes calldata) {
        return ERC2771ContextUpgradeable._msgData();
    }
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


// File contracts/Creator/CreatorFactory.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;










/// @title CreatorFactory - Manage creators and DApps wallets
/// @dev Main feature
///      - Creator and DApp creation and modification
///      - Reward(ERC20) distribution to each Creator
contract CreatorFactory is ICreatorFactory, ERC2771Context, NextOwnablePausable {
    using SafeERC20 for IERC20;

    /// @notice An trust forwarder address
    address private immutable _trustedForwarder;

    /// @notice An address of the CreatorBeacon contract
    address public immutable creatorBeacon;

    /// @notice An address of the ItemIssuance contract
    ItemIssuance public immutable itemIssuance;

    /// @notice An address to set as owner when creating a dApp
    address private _dAppOwner;

    /// @notice Array of creator information
    Creator[] private _creators;

    /// @notice Mapping of creator address to creator id
    mapping(address => uint32) private _creatorId; // [creator address] = creator id

    /// @notice Array of dApp information
    DApp[] private _dApps;

    /// @notice Mapping of dApp address to dApp id
    mapping(address => uint32) private _dAppId; // [dApp address] = dApp id

    /// @notice Check if the Creator with the given id exists
    modifier whenCreatorExists(uint32 id) {
        require(1 <= id && id <= _creators.length, "CreatorFactory/invalidCreatorId: given a non-existent id");
        _;
    }

    /// @notice Check if the DApp with the given id exists
    modifier whenDAppExists(uint32 id) {
        require(1 <= id && id <= _dApps.length, "CreatorFactory/invalidDAppId: given a non-existent id");
        _;
    }

    modifier validAddress(address addr) {
        require(addr != address(0), "CreatorFactory/validAddress: couldn't be zero address");
        _;
    }

    constructor(
        address trustedForwarder,
        address dAppOwner_,
        address creatorBeacon_,
        ItemIssuance itemIssuance_
    )
        validAddress(trustedForwarder)
        validAddress(dAppOwner_)
        validAddress(creatorBeacon_)
        validAddress(address(itemIssuance_))
        ERC2771Context(trustedForwarder)
    {
        _trustedForwarder = trustedForwarder;
        _dAppOwner = dAppOwner_;
        creatorBeacon = creatorBeacon_;
        itemIssuance = itemIssuance_;
    }

    receive() external payable {}

    /// @notice Create a new creator wallet
    /// @param name Name of the creator
    /// @param owners Array of owner addresses
    /// @param threshold Number of signatures required to execute a transaction
    function addCreator(string calldata name, address[] memory owners, uint256 threshold) external whenExecutable {
        address account = MinProxy.createBeaconProxy(creatorBeacon);
        CreatorWallet(payable(account)).initialize(owners, threshold);
        _creators.push(Creator({ name: name, account: account }));
        _creatorId[address(account)] = uint32(_creators.length);

        emit CreatorAdded(uint32(_creators.length), name, account);
    }

    /// @notice Allocate reward(NXPC, ERC20s) to a creator
    /// @param creatorAddress_ Creator address to receive the token
    /// @param nxpcAmount Amount of NXPC to allocate
    /// @param tokens Array of ERC20 token addresses to allocate
    /// @param amounts Array of ERC20 token amounts to allocate
    function allocateReward(
        address payable creatorAddress_,
        uint256 nxpcAmount,
        IERC20[] calldata tokens,
        uint256[] calldata amounts
    ) external onlyOwner {
        _allocateReward(creatorAddress_, nxpcAmount, tokens, amounts);
    }

    /// @notice Batch function of allocateReward
    /// @param rewards Array of Reward struct
    function allocateRewardBatch(Reward[] calldata rewards) external onlyOwner {
        uint256 rewardsLength = rewards.length;
        for (uint256 i; i < rewardsLength; ) {
            _allocateReward(rewards[i].creatorAddress, rewards[i].nxpcAmount, rewards[i].tokens, rewards[i].amounts);
            unchecked {
                i++;
            }
        }
    }

    /// @notice Create a new DApp wallet
    /// @param creatorId_ Creator id to create a dApp
    /// @param name Name of the dApp
    /// @param executor Address of the executor
    function addDApp(
        uint32 creatorId_,
        string calldata name,
        address executor
    ) external whenExecutable whenCreatorExists(creatorId_) {
        DAppRewardAllocationWallet dApp_ = new DAppRewardAllocationWallet(_trustedForwarder);
        dApp_.grantExecutor(executor);
        dApp_.transferOwnership(_dAppOwner);
        _dApps.push(DApp({ creatorId: creatorId_, isActive: true, name: name, account: address(dApp_) }));
        _dAppId[address(dApp_)] = uint32(_dApps.length);

        emit DAppAdded(uint32(_dApps.length), name, address(dApp_));
    }

    /// @notice Set name of a creator
    /// @param id Creator id to set name
    /// @param newName New name of the creator
    function setCreatorName(uint32 id, string calldata newName) external whenExecutable {
        emit CreatorNameChanged(id, _creators[id - 1].name, newName);
        _creators[id - 1].name = newName;
    }

    /// @notice Set name of a dApp
    /// @param id DApp id to set name
    /// @param newName New name of the dApp
    function setDAppName(uint32 id, string calldata newName) external whenExecutable {
        emit DAppNameChanged(id, _dApps[id - 1].name, newName);
        _dApps[id - 1].name = newName;
    }

    /// @notice Set DApp owner
    /// @param newDAppOwner New DApp owner address
    function setDAppOwner(address newDAppOwner) external onlyOwner {
        emit DAppOwnerChanged(_dAppOwner, newDAppOwner);
        _dAppOwner = newDAppOwner;
    }

    /// @notice Set DApp activation
    /// @param id DApp id to set activation
    /// @param isActive New activation status of the dApp
    function setDAppActivation(uint32 id, bool isActive) external whenExecutable whenDAppExists(id) {
        _dApps[id - 1].isActive = isActive;
        emit DAppActivationChanged(id, isActive);
    }

    /// @notice Set creator of dApp
    /// @param dAppId_ dApp id to set creator
    /// @param creatorId_ Creator id to set creator of dApp
    function setCreatorOfDApp(
        uint32 dAppId_,
        uint32 creatorId_
    ) external whenExecutable whenCreatorExists(creatorId_) whenDAppExists(dAppId_) {
        _dApps[dAppId_ - 1].creatorId = creatorId_;
        emit CreatorOfDAppChanged(dAppId_, creatorId_);
    }

    /// @notice Get dApp owner
    /// @return address Address of dApp owner
    function dAppOwner() external view returns (address) {
        return _dAppOwner;
    }

    /// @notice Get creator address by dApp address
    /// @param dAppAddress_ dApp address to get creator address
    /// @return address Address of dApp's creator
    function creatorAddressOfDApp(address dAppAddress_) external view returns (address) {
        return creatorAddress(creatorIdOfDApp(dAppAddress_));
    }

    /// @notice Get creator address by dApp id
    /// @param dAppId_ dApp id to get creator address
    /// @return address Address of dApp's creator
    function creatorAddressOfDApp(uint32 dAppId_) external view returns (address) {
        return creatorAddress(creatorIdOfDApp(dAppId_));
    }

    /// @notice Get creator name by creator address
    /// @param creatorAddress_ Creator address to get creator name
    /// @return string Name of creator
    function creatorName(address creatorAddress_) external view returns (string memory) {
        return creatorName(creatorId(creatorAddress_));
    }

    /// @notice Get dApp address by dApp id
    /// @param dAppId_ dApp id to get dApp address
    /// @return address Address of dapp
    function dAppAddress(uint32 dAppId_) external view whenDAppExists(dAppId_) returns (address) {
        return _dApps[dAppId_ - 1].account;
    }

    /// @notice Get dApp name by dApp address
    /// @param dAppAddress_ dApp address to get dApp name
    /// @return string Name of dApp
    function dAppName(address dAppAddress_) external view returns (string memory) {
        return dAppName(dAppId(dAppAddress_));
    }

    /// @notice Get connection status between creator and dApp by creator id and dApp address
    /// @param creatorId_ Creator id to check connection status
    /// @param dAppAddress_ dApp address to check connection status
    /// @return bool State of connection creator with dApp
    function isConnected(uint32 creatorId_, address dAppAddress_) external view returns (bool) {
        return isConnected(creatorId_, _dAppId[dAppAddress_]);
    }

    /// @notice Get connection status between creator and dApp by creator address and dApp id
    /// @param creatorAddress_ Creator address to check connection status
    /// @param dAppId_ dApp id to check connection status
    /// @return bool State of connection creator with dApp
    function isConnected(address creatorAddress_, uint32 dAppId_) external view returns (bool) {
        return isConnected(_creatorId[creatorAddress_], dAppId_);
    }

    /// @notice Get connection status between creator and dApp by creator address and dApp address
    /// @param creatorAddress_ Creator address to check connection status
    /// @param dAppAddress_ dApp address to check connection status
    /// @return bool State of connection creator with dApp
    function isConnected(address creatorAddress_, address dAppAddress_) external view returns (bool) {
        return isConnected(_creatorId[creatorAddress_], _dAppId[dAppAddress_]);
    }

    //// @notice Checks if a dApp is active
    /// @param dAppId_ The ID of the dApp to check
    /// @return bool Boolean indicating whether the specified DApp is active or not
    function isActiveDApp(uint32 dAppId_) public view returns (bool) {
        return _dApps[dAppId_ - 1].isActive;
    }

    /// @notice Get creator address by creator id
    /// @param creatorId_ Creator id to get creator address
    /// @return address Address of creator
    function creatorAddress(uint32 creatorId_) public view whenCreatorExists(creatorId_) returns (address) {
        return _creators[creatorId_ - 1].account;
    }

    /// @notice Get creatorId by creatorAddress
    /// @param creatorAddress_ Creator address to get creator id
    /// @return creatorId_ Creator Id of creator
    function creatorId(address creatorAddress_) public view returns (uint32 creatorId_) {
        creatorId_ = _creatorId[creatorAddress_];
        require(creatorId_ != 0, "CreatorFactory/invalidCreatorAddress: given a non-existent address");
    }

    /// @notice Get creator name by creatorId
    /// @param creatorId_ Creator id to get creator name
    /// @return string Name of creator
    function creatorName(uint32 creatorId_) public view whenCreatorExists(creatorId_) returns (string memory) {
        return _creators[creatorId_ - 1].name;
    }

    /// @notice Get dApp id by dApp address
    /// @param dAppAddress_ dApp address to get dApp id
    /// @return dAppId_ Id of dApp
    function dAppId(address dAppAddress_) public view returns (uint32 dAppId_) {
        dAppId_ = _dAppId[dAppAddress_];
        require(dAppId_ != 0, "CreatorFactory/invalidDAppAddress: given a non-existent address");
    }

    /// @notice Get dApp name by dApp id
    /// @param dAppId_ dApp id to get dApp name
    /// @return string Name of dApp
    function dAppName(uint32 dAppId_) public view whenDAppExists(dAppId_) returns (string memory) {
        return _dApps[dAppId_ - 1].name;
    }

    /// @notice Get creator id by dApp address
    /// @param dAppAddress_ dApp address to get creator id
    /// @return uint32 Creator id of dApp
    function creatorIdOfDApp(address dAppAddress_) public view returns (uint32) {
        return creatorIdOfDApp(dAppId(dAppAddress_));
    }

    /// @notice Get creator id by dApp id
    /// @param dAppId_ dApp id to get creator id
    /// @return uint32 Creator id of dApp
    function creatorIdOfDApp(uint32 dAppId_) public view whenDAppExists(dAppId_) returns (uint32) {
        return _dApps[dAppId_ - 1].creatorId;
    }

    /// @notice Get connection status between creator and dApp by creator id and dApp id
    /// @param creatorId_ Creator id to check connection status
    /// @param dAppId_ dApp id to check connection status
    /// @return bool State of connection creator with dApp
    function isConnected(uint32 creatorId_, uint32 dAppId_) public view returns (bool) {
        if (0 == creatorId_ || creatorId_ > _creators.length) return false;
        if (0 == dAppId_ || dAppId_ > _dApps.length) return false;
        return creatorId_ == _dApps[dAppId_ - 1].creatorId;
    }

    function _allocateReward(
        address payable creatorAddress_,
        uint256 nxpcAmount,
        IERC20[] calldata tokens,
        uint256[] calldata amounts
    ) internal whenCreatorExists(creatorId(creatorAddress_)) {
        uint256 tokensLength = tokens.length;
        require(tokensLength == amounts.length, "CreatorFactory/invalidLength: given arrays have different lengths");
        if (nxpcAmount > 0) {
            (bool success, ) = creatorAddress_.call{ value: nxpcAmount }("");
            require(success, "CreatorFactory/invalidAmount: failed to allocate NXPC");
            emit NXPCRewardAllocated(creatorAddress_, nxpcAmount);
        }
        for (uint256 i; i < tokensLength; ) {
            tokens[i].safeTransfer(creatorAddress_, amounts[i]);
            emit ERC20RewardAllocated(creatorAddress_, tokens[i], amounts[i]);
            unchecked {
                i++;
            }
        }
    }

    /* trivial overrides */
    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }
}
