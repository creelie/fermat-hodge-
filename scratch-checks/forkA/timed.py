# usage: python3 timed.py outfile errfile cmd args...  (elapsed time and peak RSS of the child, to errfile)
import sys, subprocess, time, resource
out, err = sys.argv[1], sys.argv[2]
t = time.time()
with open(out, 'w') as fo, open(err, 'w') as fe:
    r = subprocess.run(sys.argv[3:], stdout=fo, stderr=fe)
    fe.write('rc=%d elapsed=%.1fs maxrss=%dMB\n' % (r.returncode, time.time() - t, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024))
