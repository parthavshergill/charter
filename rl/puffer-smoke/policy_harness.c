// Prints what PufferLib's own CPU net computes, to check policy_reader.py against.
#include "puffercpu.c"

int main(int argc, char** argv) {
    int obs_n = atoi(argv[2]), hid = atoi(argv[3]), layers = atoi(argv[4]), act_n = atoi(argv[5]);
    Weights* weights = load_weights(argv[1]);
    int sizes[1] = {act_n};
    PufferNet* net = make_puffernet(weights, 1, obs_n, hid, layers, sizes, 1);
    float* obs = calloc(obs_n, sizeof(float));
    for (int i = 0; i < obs_n; i++) {
        obs[i] = (i % 7) / 7.0f;
    }
    float action = 0, term = 0;
    unsigned char* mask = malloc(act_n);
    memset(mask, 1, act_n);
    for (int step = 0; step < 3; step++) {
        forward_puffernet(net, obs, &action, mask, &term);
        printf("c  step %d", step);
        for (int o = 0; o < act_n + 1; o++) {
            printf(" %.4f", net->decoder->output[o]);
        }
        printf("\n");
    }
    return 0;
}
