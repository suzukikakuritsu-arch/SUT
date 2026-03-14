# 定理4-1：最小非退化黄金比証明
def theorem4_1_complete_proof(max_norm=5):
    """鈴木黄金定理4完全実装"""
    minimal_solution = None
    min_norm = float('inf')
    
    for a in range(1, max_norm+1):  # a≠0
        for b in range(-max_norm, max_norm+1):
            D = b**2 + 4*a
            if D <= 0: continue  # 実固有値
            lambda1 = (b + np.sqrt(D))/2
            lambda2 = (b - np.sqrt(D))/2
            if lambda1 > 1 and abs(lambda2) < 1:  # 安定階層
                norm = abs(a) + abs(b)
                if norm < min_norm:
                    min_norm = norm
                    minimal_solution = (a,b,lambda1)
    
    return minimal_solution  # (1,1,φ) ✓

assert theorem4_1_complete_proof()[2] == PHI
