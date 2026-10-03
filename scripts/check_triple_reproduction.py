"""Reproduction regressions: UNCONDITIONAL exact algebra and orchestration.

No analytic certificate. Nested harness tests mock suite execution, avoiding
recursive discovery; formal rational scales do not approximate real logarithms.
"""
from contextlib import ExitStack, redirect_stdout, redirect_stderr
from copy import deepcopy
from fractions import Fraction as Q
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import reproduce_triple as runner
import triple_normalization as algebra


def evaluate(term, values):
    value = Q(term['coefficient'])
    for name, power in term['powers'].items():
        exponent = Q(power)
        assert exponent.denominator == 1
        value *= values[name]**int(exponent)
    return value


class TripleReproductionChecks(unittest.TestCase):
    def test_boundary_masses_and_sector_incidence(self):
        r = algebra.generate(); b = r['boundary_assembly']
        # Independent integration-by-parts recurrence from I_0=1/2.
        moments = [Q(1, 2)]
        for k in (1, 2): moments.append(k*moments[-1]/2)
        self.assertEqual([Q(b['moments'][str(k)]) for k in range(3)], moments)
        self.assertEqual(Q(b['quadrant_origin']), moments[0]**2)
        self.assertEqual(Q(b['quadrant_ray']), sum(moments[:2]))
        directions = {tuple(x['direction']) for x in b['rays']}
        self.assertEqual(directions, {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)})
        self.assertEqual(sum(x['incidence'] for x in b['rays']), 12)
        for row in b['rays']:
            self.assertEqual(Q(row['native_density_coefficient']), Q(3,2))
            self.assertEqual(Q(row['normalized_density_coefficient']), 1)

    def test_normalization_and_finite_height_specialization(self):
        r = algebra.generate(); n = r['normalization']; c = r['critical_parameter_specialization']
        for T,q,b,p in ((Q(100),Q(7),Q(5),Q(6)), (Q(200),Q(11),Q(8),Q(7))):
            v = {'T': T, 'q': q}
            native = evaluate(n['native_observable_coefficient'], v)
            assembled = evaluate(n['assembled_observable_coefficient'], v)
            self.assertEqual(native, 8/(T*q))
            self.assertEqual(assembled, 16/(3*T*q))
            self.assertEqual(Q(n['factor'])*native, assembled)
            LT = b/p; profile = Q(c['profile_at_zero_gaps_in_units_of_pi'])*p/2
            self.assertEqual(native*profile*T*LT, 3*b/(2*q))
            self.assertEqual(assembled*profile*T*LT, b/q)
            self.assertNotEqual(b/q, Q(c['limits']['assembled']))
        self.assertEqual(Q(n['factor'])*Q(n['native_origin']), 1)

    def test_each_named_error_and_exact_scaling(self):
        errors = algebra.generate()['errors']
        for b,L,v,w,w1,wp,c1,l1 in (
            map(Q,(3,5,2,1,4,7,2,3)), map(Q,(9,2,1,0,3,1,4,2))):
            values = dict(b=b,L=L,decay=v,W_inf=w,W_1=w1,Wprime_inf=wp,phi_C1=c1,phi_L1=l1)
            expected = [c1*(1+w+w1)*(1/b+v*L**3), l1*(w+wp)*v*L**3]
            for error,want in zip(errors,expected,strict=True):
                before = sum(evaluate(t,values) for t in error['before_normalization'])
                after = sum(evaluate(t,values) for t in error['after_exact_scaling'])
                self.assertEqual(before,want)
                self.assertEqual(after,Q(2,3)*want)
        self.assertEqual([e['id'] for e in errors], ['E_signed','E_kernel'])

    def test_partitions_and_fourier_reconstruction(self):
        r=algebra.generate()
        self.assertEqual(len(r['sine_partitions']),5)
        # Independent coefficients of the five physical partition transforms.
        rows=r['sine_partitions']
        self.assertEqual(rows[0]['fourier_basis'], {'planar_one':1})
        self.assertEqual(rows[-1]['fourier_basis']['origin'],1)
        self.assertEqual(rows[-1]['fourier_basis']['cycle_overlap'],2)
        total={}
        for row in rows:
            for key,value in row['fourier_basis'].items(): total[key]=total.get(key,0)+value
        self.assertEqual(total,r['sine_fourier']['sum'])
        # Within support, the remaining planar density cancels; outside it need not.
        def density(x,y):
            h=max(abs(x),abs(y),abs(x+y))
            tau=lambda z:max(Q(0),1-abs(z))
            basis={'planar_one':1,'triangle_xi':tau(x),'triangle_eta':tau(y),
                   'triangle_sum':tau(x+y),'cycle_overlap':max(Q(0),1-h)}
            return sum(total[k]*v for k,v in basis.items())
        for x,y in ((Q(0),Q(0)),(Q(1,2),Q(-1,4)),(Q(1),Q(-1))):
            self.assertEqual(density(x,y),0)
        self.assertEqual(density(Q(3,4),Q(3,4)),Q(1,2))
        self.assertFalse(r['domain']['outer_boundary_included'])

    def test_determinism_and_source_locators(self):
        r=algebra.generate()
        self.assertNotIn('T^a', algebra.json_text(r))
        self.assertNotIn('T^a', algebra.markdown(r))
        self.assertEqual(r['definitions']['decay'], 'B^(-kappa)')
        self.assertEqual(algebra.json_text(r),algebra.json_text(algebra.generate()))
        self.assertEqual(algebra.markdown(r),algebra.markdown(algebra.generate()))
        self.assertEqual(json.loads(algebra.json_text(r)),r)
        for mutate in ('label','claim','support'):
            bad=deepcopy(r)
            if mutate=='label': bad['normalization']['source']['label']='missing-label'
            if mutate=='claim': bad['normalization']['source']['claim_id']='MISSING'
            if mutate=='support': bad['assumptions']=['UNCONDITIONAL']
            with self.assertRaises(ValueError): algebra.validate_sources(bad)

    def test_output_protection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'repo'; root.mkdir()
            with self.assertRaises(ValueError): runner.prepare_output(root,root/'proofs/new')
            out=runner.prepare_output(root,None)
            (out/'keep').write_text('preserve')
            with self.assertRaises(ValueError): runner.prepare_output(root,out)
            self.assertEqual((out/'keep').read_text(),'preserve')
            self.assertNotEqual(out,runner.prepare_output(root,None))

    def test_test_discovery_failures(self):
        self.assertEqual(runner.check_test_log('Ran 100 tests in 1s\nOK\n',96),100)
        for text in ('Ran 0 tests in 0s\nOK\n','Ran 95 tests in 1s\nOK\n',
                     'Ran 96 tests in 1s\nOK (skipped=1)\n',
                     'Ran 96 tests in 1s\nFAILED\n','OK\n'):
            with self.assertRaises(RuntimeError): runner.check_test_log(text,96)

    def test_environment_failures_and_dirty_tree(self):
        with patch.object(runner.sys,'version_info',(3,11)):
            with self.assertRaisesRegex(RuntimeError,'Python 3.12'):
                runner.collect_environment(runner.ROOT,None,{},True,False)
        with patch.object(runner.shutil,'which',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'missing prerequisite: git'):
                runner.source_state(runner.ROOT,None,{})
        state={'commit':'abc','dirty':True,'git_status':[' M README.md']}
        with patch.object(runner,'source_state',return_value=state):
            with self.assertRaisesRegex(RuntimeError,'dirty source'):
                runner.collect_environment(runner.ROOT,None,{'source':{}},True,True)
        with patch.object(runner,'source_state',return_value=state), \
             patch.object(runner,'execute',return_value='git version'), \
             patch.object(runner.shutil,'which',side_effect=lambda x: '/git' if x=='git' else None):
            with self.assertRaisesRegex(RuntimeError,'missing prerequisite: pdflatex'):
                runner.collect_environment(runner.ROOT,None,{'source':{},'environment':{}},False,False)
            self.assertEqual(runner.collect_environment(runner.ROOT,None,
                             {'source':{},'environment':{}},True,False),{})

    def test_failed_subprocess_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp); m={'stages':[]}
            with self.assertRaises(RuntimeError):
                runner.execute(m,out,'failure',[runner.sys.executable,'-c',
                               'print("retained diagnostic"); raise SystemExit(7)'],out)
            self.assertIn('retained diagnostic',(out/'logs/failure.log').read_text())
            self.assertEqual(m['stages'][0]['returncode'],7)

    def test_pdf_diagnostics_and_process_failure(self):
        for mode in ('references','process','missing','pass'):
            with tempfile.TemporaryDirectory() as tmp:
                out=Path(tmp); m={'stages':[],'pdf':{'status':'not_run'}}
                def execute(manifest,out,name,command,cwd):
                    self.assertIn('-no-shell-escape',command)
                    if mode=='process': raise RuntimeError('failed TeX')
                    log='Output written on triple_explicit_formula.pdf (34 pages, 1 bytes).\n'
                    if mode=='references': log+='LaTeX Warning: Reference `x` undefined.\n'
                    if mode=='pass': log+='Overfull box\n'
                    (cwd/'triple_explicit_formula.log').write_text(log)
                    if mode!='missing': (cwd/'triple_explicit_formula.pdf').write_bytes(b'%PDF-fixture')
                with patch.object(runner,'execute',side_effect=execute), redirect_stdout(io.StringIO()):
                    if mode=='pass':
                        runner.build_pdf(runner.ROOT,out,m,{'pdflatex':'/tex'})
                        self.assertEqual(m['pdf']['pages'],34)
                        self.assertEqual(m['pdf']['warnings'],['Overfull box'])
                    else:
                        with self.assertRaises(RuntimeError): runner.build_pdf(runner.ROOT,out,m,{'pdflatex':'/tex'})
                        self.assertEqual(m['pdf']['status'],'fail')

    def run_mocked(self,out,**overrides):
        state={'commit':'snapshot','dirty':False,'git_status':[]}
        def env(root,out,manifest,checks_only,require_clean):
            manifest['source'].update(state)
            return {}
        defaults={'collect_environment':env,'run_checks':lambda *args:None,
                  'build_pdf':lambda *args:None,'source_state':lambda *args:state}
        defaults.update(overrides)
        with ExitStack() as stack:
            for name,effect in defaults.items():
                stack.enter_context(patch.object(runner,name,side_effect=effect))
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(redirect_stderr(io.StringIO()))
            return runner.reproduce(runner.ROOT,out,checks_only=True,require_clean=True)

    def test_partial_manifest_and_output_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp); m=self.run_mocked(out)
            self.assertEqual(m['status'],'partial')
            self.assertEqual(m['pdf']['status'],'skipped')
            self.assertEqual(m['records']['triple_audit']['claims'],34)
            self.assertEqual(json.loads((out/'manifest.json').read_text()),m)
            for path,digest in m['outputs'].items(): self.assertEqual(runner.sha256(out/path),digest)
            self.assertNotIn('manifest.json',m['outputs'])

    def test_failed_audit_prevents_artifacts(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            m=self.run_mocked(out,validate_records=RuntimeError('stale audit'))
            self.assertEqual(m['status'],'fail')
            self.assertEqual(m['records']['status'],'fail')
            self.assertFalse((out/'triple-normalization.json').exists())
            self.assertTrue((out/'manifest.json').exists())

    def test_source_changes_reject_success(self):
        for kind in ('git','inputs'):
            with tempfile.TemporaryDirectory() as tmp:
                overrides={}
                if kind=='git':
                    overrides['source_state']=lambda *args: {'commit':'changed','dirty':False,'git_status':[]}
                else:
                    values=iter([{'source':'before'},{'source':'after'}])
                    overrides['input_hashes']=lambda *args:next(values)
                m=self.run_mocked(Path(tmp),**overrides)
                self.assertEqual(m['status'],'fail')
                self.assertIn('changed during reproduction',m['error'])


if __name__=='__main__':
    unittest.main(verbosity=2)
