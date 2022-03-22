#!/bin/sh
exec watchexec -w FairTermination.lagda.md "(make && echo DONE)"
