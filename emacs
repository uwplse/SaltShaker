(require 'package)
(package-initialize)
(setq package-enable-at-startup nil)

(setq package-archives '(("melpa" . "http://melpa.milkbox.net/packages/")
                         ("org" . "http://orgmode.org/elpa/")
                         ("gnu" . "http://elpa.gnu.org/packages/")))

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))
(require 'use-package)
(setq use-package-always-ensure t)

(load-file "/ProofGeneral/generic/proof-site.el")

(use-package evil
  :config
  (progn
    (evil-mode 1)
    (define-key evil-normal-state-map "L" 'proof-assert-next-command-interactive)
    (define-key evil-normal-state-map "H" 'proof-undo-last-successful-command)
    (define-key evil-normal-state-map "K" 'proof-goto-point)))

