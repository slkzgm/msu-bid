

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


// File @openzeppelin/contracts/utils/cryptography/MerkleProof.sol@v4.8.1

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/cryptography/MerkleProof.sol)

pragma solidity ^0.8.0;

/**
 * @dev These functions deal with verification of Merkle Tree proofs.
 *
 * The tree and the proofs can be generated using our
 * https://github.com/OpenZeppelin/merkle-tree[JavaScript library].
 * You will find a quickstart guide in the readme.
 *
 * WARNING: You should avoid using leaf values that are 64 bytes long prior to
 * hashing, or use a hash function other than keccak256 for hashing leaves.
 * This is because the concatenation of a sorted pair of internal nodes in
 * the merkle tree could be reinterpreted as a leaf value.
 * OpenZeppelin's JavaScript library generates merkle trees that are safe
 * against this attack out of the box.
 */
library MerkleProof {
    /**
     * @dev Returns true if a `leaf` can be proved to be a part of a Merkle tree
     * defined by `root`. For this, a `proof` must be provided, containing
     * sibling hashes on the branch from the leaf to the root of the tree. Each
     * pair of leaves and each pair of pre-images are assumed to be sorted.
     */
    function verify(
        bytes32[] memory proof,
        bytes32 root,
        bytes32 leaf
    ) internal pure returns (bool) {
        return processProof(proof, leaf) == root;
    }

    /**
     * @dev Calldata version of {verify}
     *
     * _Available since v4.7._
     */
    function verifyCalldata(
        bytes32[] calldata proof,
        bytes32 root,
        bytes32 leaf
    ) internal pure returns (bool) {
        return processProofCalldata(proof, leaf) == root;
    }

    /**
     * @dev Returns the rebuilt hash obtained by traversing a Merkle tree up
     * from `leaf` using `proof`. A `proof` is valid if and only if the rebuilt
     * hash matches the root of the tree. When processing the proof, the pairs
     * of leafs & pre-images are assumed to be sorted.
     *
     * _Available since v4.4._
     */
    function processProof(bytes32[] memory proof, bytes32 leaf) internal pure returns (bytes32) {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _hashPair(computedHash, proof[i]);
        }
        return computedHash;
    }

    /**
     * @dev Calldata version of {processProof}
     *
     * _Available since v4.7._
     */
    function processProofCalldata(bytes32[] calldata proof, bytes32 leaf) internal pure returns (bytes32) {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _hashPair(computedHash, proof[i]);
        }
        return computedHash;
    }

    /**
     * @dev Returns true if the `leaves` can be simultaneously proven to be a part of a merkle tree defined by
     * `root`, according to `proof` and `proofFlags` as described in {processMultiProof}.
     *
     * CAUTION: Not all merkle trees admit multiproofs. See {processMultiProof} for details.
     *
     * _Available since v4.7._
     */
    function multiProofVerify(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) internal pure returns (bool) {
        return processMultiProof(proof, proofFlags, leaves) == root;
    }

    /**
     * @dev Calldata version of {multiProofVerify}
     *
     * CAUTION: Not all merkle trees admit multiproofs. See {processMultiProof} for details.
     *
     * _Available since v4.7._
     */
    function multiProofVerifyCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32 root,
        bytes32[] memory leaves
    ) internal pure returns (bool) {
        return processMultiProofCalldata(proof, proofFlags, leaves) == root;
    }

    /**
     * @dev Returns the root of a tree reconstructed from `leaves` and sibling nodes in `proof`. The reconstruction
     * proceeds by incrementally reconstructing all inner nodes by combining a leaf/inner node with either another
     * leaf/inner node or a proof sibling node, depending on whether each `proofFlags` item is true or false
     * respectively.
     *
     * CAUTION: Not all merkle trees admit multiproofs. To use multiproofs, it is sufficient to ensure that: 1) the tree
     * is complete (but not necessarily perfect), 2) the leaves to be proven are in the opposite order they are in the
     * tree (i.e., as seen from right to left starting at the deepest layer and continuing at the next layer).
     *
     * _Available since v4.7._
     */
    function processMultiProof(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32[] memory leaves
    ) internal pure returns (bytes32 merkleRoot) {
        // This function rebuild the root hash by traversing the tree up from the leaves. The root is rebuilt by
        // consuming and producing values on a queue. The queue starts with the `leaves` array, then goes onto the
        // `hashes` array. At the end of the process, the last hash in the `hashes` array should contain the root of
        // the merkle tree.
        uint256 leavesLen = leaves.length;
        uint256 totalHashes = proofFlags.length;

        // Check proof validity.
        require(leavesLen + proof.length - 1 == totalHashes, "MerkleProof: invalid multiproof");

        // The xxxPos values are "pointers" to the next value to consume in each array. All accesses are done using
        // `xxx[xxxPos++]`, which return the current value and increment the pointer, thus mimicking a queue's "pop".
        bytes32[] memory hashes = new bytes32[](totalHashes);
        uint256 leafPos = 0;
        uint256 hashPos = 0;
        uint256 proofPos = 0;
        // At each step, we compute the next hash using two values:
        // - a value from the "main queue". If not all leaves have been consumed, we get the next leaf, otherwise we
        //   get the next hash.
        // - depending on the flag, either another value for the "main queue" (merging branches) or an element from the
        //   `proof` array.
        for (uint256 i = 0; i < totalHashes; i++) {
            bytes32 a = leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++];
            bytes32 b = proofFlags[i] ? leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++] : proof[proofPos++];
            hashes[i] = _hashPair(a, b);
        }

        if (totalHashes > 0) {
            return hashes[totalHashes - 1];
        } else if (leavesLen > 0) {
            return leaves[0];
        } else {
            return proof[0];
        }
    }

    /**
     * @dev Calldata version of {processMultiProof}.
     *
     * CAUTION: Not all merkle trees admit multiproofs. See {processMultiProof} for details.
     *
     * _Available since v4.7._
     */
    function processMultiProofCalldata(
        bytes32[] calldata proof,
        bool[] calldata proofFlags,
        bytes32[] memory leaves
    ) internal pure returns (bytes32 merkleRoot) {
        // This function rebuild the root hash by traversing the tree up from the leaves. The root is rebuilt by
        // consuming and producing values on a queue. The queue starts with the `leaves` array, then goes onto the
        // `hashes` array. At the end of the process, the last hash in the `hashes` array should contain the root of
        // the merkle tree.
        uint256 leavesLen = leaves.length;
        uint256 totalHashes = proofFlags.length;

        // Check proof validity.
        require(leavesLen + proof.length - 1 == totalHashes, "MerkleProof: invalid multiproof");

        // The xxxPos values are "pointers" to the next value to consume in each array. All accesses are done using
        // `xxx[xxxPos++]`, which return the current value and increment the pointer, thus mimicking a queue's "pop".
        bytes32[] memory hashes = new bytes32[](totalHashes);
        uint256 leafPos = 0;
        uint256 hashPos = 0;
        uint256 proofPos = 0;
        // At each step, we compute the next hash using two values:
        // - a value from the "main queue". If not all leaves have been consumed, we get the next leaf, otherwise we
        //   get the next hash.
        // - depending on the flag, either another value for the "main queue" (merging branches) or an element from the
        //   `proof` array.
        for (uint256 i = 0; i < totalHashes; i++) {
            bytes32 a = leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++];
            bytes32 b = proofFlags[i] ? leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++] : proof[proofPos++];
            hashes[i] = _hashPair(a, b);
        }

        if (totalHashes > 0) {
            return hashes[totalHashes - 1];
        } else if (leavesLen > 0) {
            return leaves[0];
        } else {
            return proof[0];
        }
    }

    function _hashPair(bytes32 a, bytes32 b) private pure returns (bytes32) {
        return a < b ? _efficientHash(a, b) : _efficientHash(b, a);
    }

    function _efficientHash(bytes32 a, bytes32 b) private pure returns (bytes32 value) {
        /// @solidity memory-safe-assembly
        assembly {
            mstore(0x00, a)
            mstore(0x20, b)
            value := keccak256(0x00, 0x40)
        }
    }
}


// File contracts/Interfaces/IEquip.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;

interface IEquip {
    function transferFrom(address, address, uint256) external;

    function tokenItemId(uint256) external view returns (uint64);

    function ownerOf(uint256) external view returns (address);
}


// File contracts/Interfaces/INXPCAmountManager.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;

interface INXPCAmountManager {
    function totalSupply() external view returns (uint256);

    function addBurnedAmount(uint256 amount) external;

    function addMintedAmount(uint256 amount) external;
}


// File contracts/NXPC/NXPCDistributor.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity 0.8.19;






/// @title NXPCDistributor
/// @notice NXPCDistributor contract is a contract that crowdsources a specific set of NFTs and pays NXPC
/// to participants in proportion to their participation stake when NFT collection is completed.
contract NXPCDistributor is ERC2771Context, NextOwnablePausable {
    /// @notice Equip contract address
    IEquip public immutable equip;

    /* solhint-disable var-name-mixedcase */
    /// @notice NXPCAmountManager contract address
    INXPCAmountManager public immutable NXPCAmountManager;
    /* solhint-enable var-name-mixedcase */

    address private _vault;

    /// @notice Current status
    bool private _isStarted;

    /// @notice Current round number
    uint256 private _currentRound;

    /// @notice Basket merkle root: keccak256(keccak256(round || itemId || slotLength))
    mapping(uint256 => bytes32) private _basketMerkleRoot;

    /// @notice Reward merkle root: keccak256(keccak256(round || address || NXPCAmount))
    mapping(uint256 => bytes32) private _rewardMerkleRoot;

    /// @notice Total basket length of round
    mapping(uint256 => uint256) private _basketLength;

    /// @notice Current length of basket
    mapping(uint256 => uint256) private _currentBasketLength;

    /// @notice Claimable status of round
    mapping(uint256 => bool) private _isClaimable;

    /// @notice Claimed status of leaf
    mapping(bytes32 => bool) private _isClaimed;

    /// @notice Current length of slot
    mapping(uint256 => mapping(uint64 => uint256)) private _currentSlotLength;

    /// @notice Current status of slot
    mapping(uint256 => mapping(uint64 => bool)) private _isFullSlot;

    /// @notice Current depositor of NFT
    mapping(uint256 => mapping(uint256 => address)) private _currentDepositor;

    event SetBasket(uint256 indexed round, bytes32 indexed merkleRoot);
    event SetReward(uint256 indexed round, bytes32 indexed merkleRoot);
    event SetVault(address indexed previousVault, address indexed newVault);
    event Start(uint256 indexed round);
    event End(uint256 indexed round);
    event Deposit(uint256 indexed round, uint256 tokenId, uint64 itemId, address indexed user);
    event Withdraw(uint256 indexed round, uint256 tokenId, uint64 itemId, address indexed user);
    event Claim(uint256 indexed round, uint256 value, address indexed user);
    event BasketIsFull(uint256 indexed round);

    modifier validAddress(address addr) {
        require(addr != address(0), "NXPCDistributor/invalidAddress: couldn't be zero address");
        _;
    }

    /* solhint-disable var-name-mixedcase */
    /// @dev Need CAs for deploy this contract
    /// @param trustedForwarder Forwarder contract address
    /// @param equip_ Equip contract address
    constructor(
        address trustedForwarder,
        address equip_,
        address NXPCAmountManager_,
        address vault_
    )
        ERC2771Context(trustedForwarder)
        validAddress(trustedForwarder)
        validAddress(equip_)
        validAddress(NXPCAmountManager_)
        validAddress(vault_)
    {
        equip = IEquip(equip_);
        NXPCAmountManager = INXPCAmountManager(NXPCAmountManager_);
        _currentRound = 1;
        _vault = vault_;
    }

    /* solhint-enable var-name-mixedcase */

    /// @notice Set new merkle root and basket length of `round`
    /// @param round Number of current round or future round
    /// @param length Basket length of `round`
    /// @param merkleRoot Merkle root of basket tree
    function setBasket(uint256 round, uint256 length, bytes32 merkleRoot) external whenExecutable {
        require(
            currentRound() <= round,
            "NXPCDistributor/invalidRound: round must be greater than or equal to current round"
        );

        _setBasket(round, length, merkleRoot);
    }

    /// @notice Set new merkle root of `round`
    /// @param round Number of ended round
    /// @param merkleRoot Merkle root of reward tree
    function setReward(uint256 round, bytes32 merkleRoot) external payable whenExecutable {
        require(currentRound() > round, "NXPCDistributor/invalidRound: round must be ended");

        NXPCAmountManager.addMintedAmount(msg.value);

        _setReward(round, merkleRoot);
    }

    /// @notice Set new vault address
    /// @param newVault CA of new vault
    function setVault(address newVault) external onlyOwner validAddress(newVault) {
        require(!isStarted(), "NXPCDistributor/invalidRound: round must be ended");

        _setVault(newVault);
    }

    /// @notice Starts current round
    function start() external whenExecutable {
        _start();
    }

    /// @notice Ends current round
    function end() external whenExecutable {
        require(
            currentBasketLength(currentRound()) == basketLength(currentRound()),
            "NXPCDistributor/invalidBasket: basket isn't full"
        );

        _end();
    }

    /// @notice Ends current round
    /// @dev Must use this function for emergency cases
    function emergencyEnd() external whenExecutable {
        _end();
    }

    /// @notice Deposits `tokenId` from `user` and proves basket by `proof`
    /// @param tokenId Token id for deposit
    /// @param user EOA of depositor
    /// @param slotLength Number of current slot's limit
    /// @param proof Merkle proof of basket tree
    function deposit(
        uint256 tokenId,
        address user,
        uint256 slotLength,
        bytes32[] calldata proof
    ) external whenExecutable validAddress(user) {
        require(isStarted(), "NXPCDistributor/alreadyEnded: round must be started");

        uint64 itemId = equip.tokenItemId(tokenId);

        require(
            MerkleProof.verifyCalldata(
                proof,
                basketMerkleRoot(currentRound()),
                keccak256(bytes.concat(keccak256(abi.encode(currentRound(), itemId, slotLength))))
            ),
            "NXPCDistributor/invalidProof: basket merkle root is different"
        );

        _deposit(currentRound(), tokenId, user, slotLength);
    }

    /// @notice Batch version of {deposit}
    /// @param tokenIds Token ids array for deposit
    /// @param user EOA of depositor
    /// @param slotLength Number array of current slots' limit
    /// @param proof Merkle proof array of basket tree
    function batchDeposit(
        uint256[] calldata tokenIds,
        address user,
        uint256[] calldata slotLength,
        bytes32[][] calldata proof
    ) external whenExecutable validAddress(user) {
        require(isStarted(), "NXPCDistributor/alreadyEnded: round must be started");
        uint256 slotsLength = slotLength.length;
        require(
            tokenIds.length == slotsLength,
            "NXPCDistributor/invalidInputLength: all input arrays must have the same length"
        );
        require(
            proof.length == slotsLength,
            "NXPCDistributor/invalidInputLength: all input arrays must have the same length"
        );

        for (uint256 i; i < slotsLength; ) {
            uint64 itemId = equip.tokenItemId(tokenIds[i]);

            require(
                MerkleProof.verifyCalldata(
                    proof[i],
                    basketMerkleRoot(currentRound()),
                    keccak256(bytes.concat(keccak256(abi.encode(currentRound(), itemId, slotLength[i]))))
                ),
                "NXPCDistributor/invalidProof: basket merkle root is different"
            );

            _deposit(currentRound(), tokenIds[i], user, slotLength[i]);

            unchecked {
                i++;
            }
        }
    }

    /// @notice Withdraws `tokenId` to `user`
    /// @param tokenId Token id for withdraw
    /// @param user EOA of depositor
    function withdraw(uint256 tokenId, address user) external whenExecutable {
        require(isStarted(), "NXPCDistributor/alreadyEnded: round must be started");
        require(
            currentDepositor(currentRound(), tokenId) == user,
            "NXPCDistributor/invalidDepositor: user is not a depositor"
        );

        _withdraw(currentRound(), tokenId, user);
    }

    /// @notice Batch version of {withdraw}
    /// @param tokenIds Token ids array for withdraw
    /// @param user EOA of depositor
    function batchWithdraw(uint256[] calldata tokenIds, address user) external whenExecutable {
        require(isStarted(), "NXPCDistributor/alreadyEnded: round must be started");

        uint256 tokenIdsLength = tokenIds.length;
        for (uint256 i; i < tokenIdsLength; ) {
            require(
                currentDepositor(currentRound(), tokenIds[i]) == user,
                "NXPCDistributor/invalidDepositor: user is not a depositor"
            );

            _withdraw(currentRound(), tokenIds[i], user);

            unchecked {
                i++;
            }
        }
    }

    /// @notice Send `amount` NXPC to `user` and proves reward by `proof`
    /// @param round Number of round
    /// @param user EOA of user
    /// @param amount Amount of NXPC reward
    /// @param proof Merkle proof of reward tree
    function claim(uint256 round, address user, uint256 amount, bytes32[] calldata proof) external whenExecutable {
        require(isClaimable(round), "NXPCDistributor/notClaimable: reward has not been registered");
        require(
            MerkleProof.verifyCalldata(
                proof,
                rewardMerkleRoot(round),
                keccak256(bytes.concat(keccak256(abi.encode(round, user, amount))))
            ),
            "NXPCDistributor/invalidProof: reward merkle root is different"
        );

        _claim(round, user, amount);
    }

    /// @notice Returns number of current round
    /// @return uint256
    function currentRound() public view returns (uint256) {
        return _currentRound;
    }

    /// @notice Returns current status
    /// @return bool
    function isStarted() public view returns (bool) {
        return _isStarted;
    }

    /// @notice Returns vault contract address
    /// @return address
    function vault() public view returns (address) {
        return _vault;
    }

    /// @notice Returns basket merkle root of `round`
    /// @param round Number of round
    /// @return bytes32
    function basketMerkleRoot(uint256 round) public view returns (bytes32) {
        return _basketMerkleRoot[round];
    }

    /// @notice Returns reward merkle root of `round`
    /// @param round Number of round
    /// @return bytes32
    function rewardMerkleRoot(uint256 round) public view returns (bytes32) {
        return _rewardMerkleRoot[round];
    }

    /// @notice Returns basket length of `round`
    /// @param round Number of round
    /// @return uint256
    function basketLength(uint256 round) public view returns (uint256) {
        return _basketLength[round];
    }

    /// @notice Returns number of full slot of `round`
    /// @param round Number of round
    /// @return uint256
    function currentBasketLength(uint256 round) public view returns (uint256) {
        return _currentBasketLength[round];
    }

    /// @notice Returns claimable status of `round`
    /// @param round Number of round
    /// @return bool
    function isClaimable(uint256 round) public view returns (bool) {
        return _isClaimable[round];
    }

    /// @notice Returns claimed status of `leaf`
    /// @param leaf Merkle leaf of reward tree
    /// @return bool
    function isClaimed(bytes32 leaf) public view returns (bool) {
        return _isClaimed[leaf];
    }

    /// @notice Returns current slot length of `itemId`
    /// @param round Number of round
    /// @param itemId Item id of equip
    /// @return uint256
    function currentSlotLength(uint256 round, uint64 itemId) public view returns (uint256) {
        return _currentSlotLength[round][itemId];
    }

    /// @notice Returns true if `itemId` slot is full
    /// @param round Number of round
    /// @param itemId Item id of equip
    /// @return bool
    function isFullSlot(uint256 round, uint64 itemId) public view returns (bool) {
        return _isFullSlot[round][itemId];
    }

    /// @notice Returns depositor of `tokenId`
    /// @param round Number of round
    /// @param tokenId Token id of equip
    /// @return address
    function currentDepositor(uint256 round, uint256 tokenId) public view returns (address) {
        return _currentDepositor[round][tokenId];
    }

    /* solhint-enable func-name-mixedcase */
    /* trivial overrides */

    function _msgSender() internal view virtual override(Context, ERC2771Context) returns (address sender) {
        return ERC2771Context._msgSender();
    }

    function _msgData() internal view virtual override(Context, ERC2771Context) returns (bytes calldata) {
        return ERC2771Context._msgData();
    }

    /// @dev See {setBasket} function
    function _setBasket(uint256 round, uint256 length, bytes32 merkleRoot) private {
        require(length > 0, "NXPCDistributor/invalidLength: length must be bigger than 0");
        require(merkleRoot != 0, "NXPCDistributor/invalidMerkleRoot: merkle root must not be zero bytes");

        _basketLength[round] = length;
        _basketMerkleRoot[round] = merkleRoot;

        emit SetBasket(round, merkleRoot);
    }

    /// @dev See {setReward} function
    function _setReward(uint256 round, bytes32 merkleRoot) private {
        require(merkleRoot != 0, "NXPCDistributor/invalidMerkleRoot: merkle root must not be zero bytes");

        _rewardMerkleRoot[round] = merkleRoot;
        _isClaimable[round] = true;

        emit SetReward(round, merkleRoot);
    }

    /// @dev See {setVault} function
    function _setVault(address newVault) private {
        emit SetVault(_vault, newVault);
        _vault = newVault;
    }

    /// @dev See {start} function
    function _start() private {
        require(
            basketMerkleRoot(currentRound()) != 0,
            "NXPCDistributor/invalidMerkleRoot: basket merkle root has not been set"
        );
        require(!isStarted(), "NXPCDistributor/alreadyStarted: round must be ended");

        emit Start(currentRound());

        _isStarted = true;
    }

    /// @dev See {end} function
    function _end() private {
        require(isStarted(), "NXPCDistributor/alreadyEnded: round must be started");

        emit End(currentRound());

        unchecked {
            _currentRound++;
        }
        _isStarted = false;
    }

    /// @dev See {deposit} function
    function _deposit(uint256 round, uint256 tokenId, address user, uint256 slotLength) private {
        uint64 itemId = equip.tokenItemId(tokenId);

        require(!isFullSlot(currentRound(), itemId), "NXPCDistributor/invalidSlot: current item's slot is full");
        unchecked {
            _currentSlotLength[round][itemId]++;
        }
        _currentDepositor[round][tokenId] = user;

        if (currentSlotLength(round, itemId) == slotLength) {
            _isFullSlot[round][itemId] = true;
            _addCurrentBasketLength(round);
        }

        //slither-disable-next-line arbitrary-send-erc20
        equip.transferFrom(user, vault(), tokenId);

        emit Deposit(round, tokenId, itemId, user);
    }

    /// @dev See {withdraw} function
    function _withdraw(uint256 round, uint256 tokenId, address user) private {
        uint64 itemId = equip.tokenItemId(tokenId);

        _currentSlotLength[round][itemId]--;

        delete _currentDepositor[round][tokenId];

        if (isFullSlot(round, itemId)) {
            _isFullSlot[round][itemId] = false;
            _subCurrentBasketLength(round);
        }

        equip.transferFrom(vault(), user, tokenId);

        emit Withdraw(round, tokenId, itemId, user);
    }

    /// @dev See {claim} function
    function _claim(uint256 round, address user, uint256 amount) private {
        bytes32 leaf = keccak256(bytes.concat(keccak256(abi.encode(round, user, amount))));

        require(!isClaimed(leaf), "NXPCDistributor/alreadyClaimed: merkle leaf is already used");

        _isClaimed[leaf] = true;

        //slither-disable-next-line arbitrary-send-eth
        (bool success, ) = user.call{ value: amount }("");

        require(success, "NXPCDistributor/transferFailed: NXPC transfer failed");

        emit Claim(round, amount, user);
    }

    /// @dev See {deposit} function
    function _addCurrentBasketLength(uint256 round) private {
        unchecked {
            _currentBasketLength[round]++;
        }

        if (currentBasketLength(round) == basketLength(round)) {
            emit BasketIsFull(round);
        }
    }

    /// @dev See {withdraw} function
    function _subCurrentBasketLength(uint256 round) private {
        _currentBasketLength[round]--;
    }
}
