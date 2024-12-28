import numpy as np

def softmax_reduction_basic(x, y):
    e_x = np.exp(x)
    softmax = e_x / e_x.sum(axis=0)
    return (softmax * y).sum()

def softmax_reduction_stable(x, y):
    e_x = np.exp(x - np.max(x))
    softmax = e_x / e_x.sum(axis=0)
    return (softmax * y).sum()

def process_single_tile(
        x_tile, y_tile, online_max, online_output, online_denominator):
    old_online_max = online_max
    online_max = max(online_max, x_tile.max())
    online_output = (
        online_output * np.exp(old_online_max - online_max) +
        np.sum(np.exp(x_tile - online_max) * y_tile))
    online_denominator = (
        online_denominator * np.exp(old_online_max - online_max) +
        np.sum(np.exp(x_tile - online_max)))
    return online_max, online_output, online_denominator

def softmax_reduction_stable_online(x, y):
    online_max = float('-inf')
    online_output = 0.0
    online_denominator = 0.0
    for i in range(0, len(x), 4):
        x_tile = x[i:i+4]
        y_tile = y[i:i+4]
        online_max, online_output, online_denominator = process_single_tile(
            x_tile, y_tile, online_max, online_output, online_denominator)
    return online_output / online_denominator

def main():
    x = np.random.random(128)
    y = np.random.random(128)
    result_basic = softmax_reduction_basic(x, y)
    result_stable = softmax_reduction_stable(x, y)
    result_stable_online = softmax_reduction_stable_online(x, y)
    print(np.allclose(result_stable, result_stable_online))

if __name__ == '__main__':
    main()
