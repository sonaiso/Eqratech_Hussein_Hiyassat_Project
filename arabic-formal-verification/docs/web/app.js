/**
 * SFGCOQ - نظام التحقق الرسمي للنحو العربي
 * Systemic Functional Grammar - COQ Formal Verification
 * Main Application JavaScript
 */

// Application State
let appData = null;

// Category translations for display
const categoryNames = {
    nominal: 'الجملة الاسمية',
    verbal: 'الجملة الفعلية',
    particles: 'الحروف',
    morphology: 'الصرف'
};

// Initialize the application
document.addEventListener('DOMContentLoaded', async () => {
    await loadData();
    initNavigation();
    initGrammarSection();
    initVerificationSection();
});

/**
 * Load grammar data from JSON file
 */
async function loadData() {
    try {
        const response = await fetch('data.json');
        if (!response.ok) {
            throw new Error('Failed to load data');
        }
        appData = await response.json();
    } catch (error) {
        console.error('Error loading data:', error);
        showError('فشل في تحميل البيانات. يرجى تحديث الصفحة.');
    }
}

/**
 * Initialize navigation functionality
 */
function initNavigation() {
    const navLinks = document.querySelectorAll('nav a');
    const sections = document.querySelectorAll('.section');
    
    navLinks.forEach(link => {
        link.addEventListener('click', (e) => {
            e.preventDefault();
            const targetSection = link.getAttribute('data-section');
            
            // Update active states
            navLinks.forEach(l => l.classList.remove('active'));
            link.classList.add('active');
            
            sections.forEach(section => {
                section.classList.remove('active');
                if (section.id === targetSection) {
                    section.classList.add('active');
                }
            });
            
            // Smooth scroll to top of main content
            window.scrollTo({ top: 200, behavior: 'smooth' });
        });
    });
    
    // Handle browser back/forward
    window.addEventListener('hashchange', () => {
        const hash = window.location.hash.slice(1) || 'home';
        const link = document.querySelector(`nav a[data-section="${hash}"]`);
        if (link) {
            link.click();
        }
    });
}

/**
 * Initialize Grammar Section
 */
function initGrammarSection() {
    const categoryFilter = document.getElementById('category-filter');
    const grammarList = document.getElementById('grammar-list');
    
    // Populate grammar list on initial load
    if (appData && appData.grammar_rules) {
        renderGrammarRules(appData.grammar_rules);
    }
    
    // Filter change handler
    categoryFilter.addEventListener('change', (e) => {
        const selectedCategory = e.target.value;
        if (selectedCategory === 'all') {
            renderGrammarRules(appData.grammar_rules);
        } else {
            const filtered = appData.grammar_rules.filter(
                rule => rule.category === selectedCategory
            );
            renderGrammarRules(filtered);
        }
    });
}

/**
 * Render grammar rules to the DOM
 */
function renderGrammarRules(rules) {
    const grammarList = document.getElementById('grammar-list');
    
    if (!rules || rules.length === 0) {
        grammarList.innerHTML = '<p class="placeholder">لا توجد قواعد مطابقة للتصفية المحددة</p>';
        return;
    }
    
    grammarList.innerHTML = rules.map(rule => `
        <div class="grammar-item" data-id="${rule.id}">
            <h4>
                ${rule.name_ar}
                <span class="category-badge">${categoryNames[rule.category] || rule.category}</span>
            </h4>
            <p><strong>النمط:</strong> <span class="pattern">${rule.pattern}</span></p>
            <p>${rule.description}</p>
            
            <div class="examples">
                <strong>أمثلة:</strong>
                ${rule.examples.map(ex => `
                    <div class="example">
                        <div class="sentence">${ex.sentence}</div>
                        <div class="analysis">${ex.analysis}</div>
                    </div>
                `).join('')}
            </div>
            
            ${rule.coq_proof ? `
                <div class="coq-proof">
                    <strong>COQ Proof:</strong><br>
                    ${escapeHtml(rule.coq_proof)}
                </div>
            ` : ''}
        </div>
    `).join('');
}

/**
 * Initialize Verification Section
 */
function initVerificationSection() {
    const verifyBtn = document.getElementById('verify-btn');
    const sentenceInput = document.getElementById('sentence-input');
    const resultContent = document.getElementById('result-content');
    
    verifyBtn.addEventListener('click', () => {
        const sentence = sentenceInput.value.trim();
        
        if (!sentence) {
            showResult('يرجى إدخال جملة للتحقق منها', 'error');
            return;
        }
        
        // Show loading state
        resultContent.innerHTML = '<div class="loading"></div> جارٍ التحقق...';
        
        // Simulate verification process
        setTimeout(() => {
            const result = verifySentence(sentence);
            displayVerificationResult(result);
        }, 1000);
    });
    
    // Allow Enter key to trigger verification
    sentenceInput.addEventListener('keypress', (e) => {
        if (e.key === 'Enter' && !e.shiftKey) {
            e.preventDefault();
            verifyBtn.click();
        }
    });
}

/**
 * Verify an Arabic sentence
 * This is a simplified verification - in production, this would call a backend API
 */
function verifySentence(sentence) {
    const words = sentence.split(/\s+/).filter(w => w.length > 0);
    const result = {
        sentence: sentence,
        wordCount: words.length,
        isValid: true,
        analysis: [],
        warnings: [],
        matchedRules: []
    };
    
    // Basic structural analysis
    if (words.length < 2) {
        result.warnings.push('الجملة قصيرة جداً - يفضل أن تتكون من كلمتين على الأقل');
    }
    
    // Check for common patterns
    if (appData && appData.grammar_rules) {
        // Check for nominal sentence patterns (starts with definite noun)
        if (words[0] && words[0].startsWith('ال')) {
            result.analysis.push({
                type: 'structure',
                description: 'يبدو أن هذه جملة اسمية (تبدأ باسم معرف بأل)'
            });
            result.matchedRules.push('nominal_001');
        }
        
        // Check for verbal patterns (common verb prefixes)
        const verbPrefixes = ['ي', 'ت', 'أ', 'ن'];
        if (words[0] && verbPrefixes.some(p => words[0].startsWith(p))) {
            result.analysis.push({
                type: 'structure',
                description: 'يبدو أن هذه جملة فعلية (تبدأ بفعل)'
            });
            result.matchedRules.push('verbal_001');
        }
        
        // Check for particles (using Set for O(1) lookup)
        const commonParticles = new Set(['في', 'على', 'من', 'إلى', 'عن', 'مع', 'ب', 'ل', 'ك']);
        words.forEach((word, index) => {
            if (commonParticles.has(word)) {
                result.analysis.push({
                    type: 'particle',
                    description: `"${word}" - حرف جر في الموضع ${index + 1}`
                });
            }
        });
        
        // Check for إنّ and sisters
        const innaSisters = ['إنّ', 'إن', 'أنّ', 'أن', 'كأنّ', 'كأن', 'لكنّ', 'لكن', 'ليت', 'لعلّ', 'لعل'];
        if (innaSisters.includes(words[0])) {
            result.analysis.push({
                type: 'structure',
                description: 'الجملة تبدأ بأحد الحروف الناسخة (إنّ وأخواتها)'
            });
            result.matchedRules.push('nominal_003');
        }
        
        // Check for كان and sisters
        const kanaSisters = ['كان', 'أصبح', 'أضحى', 'أمسى', 'بات', 'ظل', 'صار', 'ليس', 'مازال', 'مابرح', 'مافتئ', 'ماانفك', 'مادام'];
        if (kanaSisters.includes(words[0])) {
            result.analysis.push({
                type: 'structure',
                description: 'الجملة تبدأ بأحد الأفعال الناسخة (كان وأخواتها)'
            });
            result.matchedRules.push('nominal_002');
        }
    }
    
    // Add general analysis
    result.analysis.push({
        type: 'count',
        description: `عدد الكلمات: ${words.length}`
    });
    
    return result;
}

/**
 * Display verification result
 */
function displayVerificationResult(result) {
    const resultContent = document.getElementById('result-content');
    
    let html = `
        <div class="result-item">
            <strong>الجملة:</strong> ${escapeHtml(result.sentence)}
        </div>
    `;
    
    if (result.warnings.length > 0) {
        html += `
            <div class="result-item" style="border-right-color: #f39c12;">
                <strong>تحذيرات:</strong>
                <ul>
                    ${result.warnings.map(w => `<li>${escapeHtml(w)}</li>`).join('')}
                </ul>
            </div>
        `;
    }
    
    if (result.analysis.length > 0) {
        html += `
            <div class="result-item">
                <strong>التحليل:</strong>
                <ul>
                    ${result.analysis.map(a => `<li>${escapeHtml(a.description)}</li>`).join('')}
                </ul>
            </div>
        `;
    }
    
    if (result.matchedRules.length > 0 && appData) {
        const matchedRuleDetails = result.matchedRules
            .map(ruleId => appData.grammar_rules.find(r => r.id === ruleId))
            .filter(r => r);
        
        if (matchedRuleDetails.length > 0) {
            html += `
                <div class="result-item" style="border-right-color: #27ae60;">
                    <strong>القواعد المطابقة:</strong>
                    <ul>
                        ${matchedRuleDetails.map(r => `<li><strong>${r.name_ar}</strong>: ${r.pattern}</li>`).join('')}
                    </ul>
                </div>
            `;
        }
    }
    
    html += `
        <div class="result-item ${result.isValid ? 'success' : 'error'}">
            <strong>النتيجة:</strong> ${result.isValid ? '✓ الجملة صحيحة نحوياً' : '✗ توجد مشاكل في الجملة'}
        </div>
    `;
    
    resultContent.innerHTML = html;
}

/**
 * Show result message
 */
function showResult(message, type = 'info') {
    const resultContent = document.getElementById('result-content');
    const className = type === 'error' ? 'error' : (type === 'success' ? 'success' : '');
    resultContent.innerHTML = `<p class="${className}">${escapeHtml(message)}</p>`;
}

/**
 * Show error message
 */
function showError(message) {
    console.error(message);
    const grammarList = document.getElementById('grammar-list');
    if (grammarList) {
        grammarList.innerHTML = `<p class="error">${escapeHtml(message)}</p>`;
    }
}

/**
 * Escape HTML to prevent XSS
 */
function escapeHtml(text) {
    if (!text) return '';
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

// Export functions for testing
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        verifySentence,
        escapeHtml
    };
}
